{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}

module DisjointSets
  ( DisjointSets
  , empty
  , find
  , union
  , unions
  , insert
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Maybe
import Data.Map.Strict (Map)
import Data.Maybe
import Data.Primitive.MutVar
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as MVector

import Prelude hiding (read)

-- | 'DisjointSets' represents a set of disjoint (non-overlapping) sets.
--
--   In nearly-constant time, you can find the smallest element of any
--   set given an element of that set (with 'find'), or you can combine
--   two sets (with 'union').
--
--   The maximum supported size of this structure is roughly 2^32 elements.
data DisjointSets s a = DisjointSets
  { toIndexVar :: {-# unpack #-} !(MutVar s (Map a Index))
  , fromIndexVar :: {-# unpack #-} !(GrowableVector s a)
  , nodesVar :: {-# unpack #-} !(GrowableVector s Node)
  }

-- | An 'empty' 'DisjointSets'.
empty :: (PrimMonad m)
  => m (DisjointSets (PrimState m) a)
empty = DisjointSets
  <$> newMutVar Map.empty
  <*> newGrowableVector 1
  <*> newGrowableVector 1
{-# inline empty #-}

-- | Insert an element into a 'DisjointSets'.
--   The element will be inserted as an equivalence class containing only
--   itself.
insert :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> a
  -> m ()
insert d a = do
  index <- sizeOf (nodesVar d)
  push (Node { parent = index, size = 1 }) (nodesVar d)
  modifyMutVar' (toIndexVar d) (Map.insert a index)
  push a (fromIndexVar d)
{-# inlineable insert #-}

-- | Returns the minimal element of the equivalence class.
find :: forall m a. (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> a
  -> m (Maybe a)
find d a = runMaybeT $ do
  ix <- (MaybeT . findIndex d) =<< MaybeT (getIndex d a)
  MaybeT (indexToValue d ix)
{-# inline find #-}

-- | Group the two elements into the same equivalence class.
--   If one or both of the elements are not present in the 'DisjointSets',
--   this returns 'False'.
union :: forall m a. (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> a
  -> a
  -> m Bool
union d x y
  -- this check ensures that `x` is the minimal element.
  | x > y = union d y x
  | otherwise = fmap isJust $ runMaybeT $ do
      xRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d x)
      yRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d y)
      if xRoot == yRoot
        then do
          pure ()
        else do
          Node{size=xRootSize} <- indexToNode d xRoot
          Node{size=yRootSize} <- indexToNode d yRoot
          let nodes = nodesVar d
          when (xRootSize < yRootSize) $ do
            swap nodes xRoot yRoot
          modify nodes (\n -> n { parent = xRoot }) yRoot
          modify nodes (\n -> n { size = xRootSize + yRootSize }) xRoot
{-# inlineable union #-}

-- | Group the elements into the same equivalence class. If any
--   of the elements are not present in the 'DisjointSets', this returns
--   'False'.
unions :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> [a]
  -> m Bool
unions d = fmap and . go
  where
    go = \case
      [] -> pure []
      [_] -> pure []
      (x:xs) -> forM xs $ \a -> union d x a
{-# inline unions #-}

--------------------------------------
-- Internal types and functions     --
--------------------------------------

type Index = Int

data Node = Node
  { parent :: {-# unpack #-} !Index
  , size :: {-# unpack #-} !Int
  }

-- get the index of an element
getIndex :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> a
  -> m (Maybe Index)
getIndex DisjointSets{toIndexVar} a = Map.lookup a <$> readMutVar toIndexVar

-- get the node corresponding to an element
getNode :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> a
  -> m (Maybe Node)
getNode d x = do
  mindex <- getIndex d x
  forM mindex $ \index -> indexToNode d index

-- get the node at an index
indexToNode :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> Index
  -> m Node
indexToNode d ix = read ix (nodesVar d)

-- get the value at an index
indexToValue :: (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> Index
  -> m (Maybe a)
indexToValue DisjointSets{fromIndexVar} ix = readMaybe ix fromIndexVar

-- Like 'find', but takes an index and returns the 'Index' of the found element.
findIndex :: forall m a. (PrimMonad m, Ord a)
  => DisjointSets (PrimState m) a
  -> Index
  -> m (Maybe Index)
-- N.B. we use path-halving
findIndex d ix = runMaybeT $ do
  let go :: Index -> MaybeT m Index
      go !x = do
        p <- parent <$> indexToNode d x
        pp <- parent <$> indexToNode d p
        if (p /= x)
          then do
            modify (nodesVar d) (\n -> n { parent = pp }) p
            go p
          else do
            pure x
  go ix

-----------------------------------------
-- Internal data structures            --
-----------------------------------------

data GrowableVector s a = GrowableVector
  { sizeVar :: {-# unpack #-} !(MutVar s Int)
  , vectorVar :: {-# unpack #-} !(MutVar s (MVector s a))
  }

sizeOf :: PrimMonad m => GrowableVector (PrimState m) a -> m Int
sizeOf g = readMutVar (sizeVar g)

newGrowableVector :: PrimMonad m => Int -> m (GrowableVector (PrimState m) a)
newGrowableVector sz = GrowableVector
  <$> newMutVar 0
  <*> (newMutVar =<< MVector.new sz)

read :: PrimMonad m => Int -> GrowableVector (PrimState m) a -> m a
read n g = flip MVector.read n =<< readMutVar (vectorVar g)

readMaybe :: PrimMonad m => Int -> GrowableVector (PrimState m) a -> m (Maybe a)
readMaybe n g = do
  sz <- sizeOf g
  if (n > 0 && n < sz)
    then Just <$> read n g
    else pure Nothing

push :: PrimMonad m => a -> GrowableVector (PrimState m) a -> m ()
push x g = do
  needsResizing <- atMaxCapacity g
  when needsResizing (resize g)

  index <- readMutVar (sizeVar g)
  readMutVar (vectorVar g) >>= \v -> MVector.write v index x

  modifyMutVar' (sizeVar g) (+ 1)

-- We always resize by a factor of 2
resize :: PrimMonad m => GrowableVector (PrimState m) a -> m ()
resize (GrowableVector sizeVar var) = do
  v <- readMutVar var
  v' <- MVector.unsafeGrow v (MVector.length v)
  writeMutVar var v'

-- Are we at max capacity?
atMaxCapacity :: (PrimMonad m)
  => GrowableVector (PrimState m) a
  -> m Bool
atMaxCapacity g = go <$> readMutVar (sizeVar g) <*> (MVector.length <$> readMutVar (vectorVar g))
  where
    go x y = x + 1 >= y

modify :: PrimMonad m
  => GrowableVector (PrimState m) a
  -> (a -> a)
  -> Int
  -> m ()
modify g f ix = readMutVar (vectorVar g) >>= \v -> MVector.modify v f ix

swap :: PrimMonad m
  => GrowableVector (PrimState m) a
  -> Int
  -> Int
  -> m ()
swap g x y = readMutVar (vectorVar g) >>= \v -> MVector.swap v x y
