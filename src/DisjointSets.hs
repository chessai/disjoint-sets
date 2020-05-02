{-# language BangPatterns #-}
{-# language DeriveAnyClass #-}
{-# language DerivingStrategies #-}
{-# language DerivingVia #-}
{-# language DuplicateRecordFields #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}

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
import Data.Vector.Unboxed.Mutable (Unbox)
import qualified Data.Map.Strict as Map

import qualified Data.Vector.Unboxed.Base as Base

import qualified Data.Vector.Generic as VClass
import qualified Data.Vector.Generic.Mutable as MClass

import qualified Data.Vector.Unboxed as Unboxed
import qualified Data.Vector.Unboxed.Mutable as MUnboxed
import qualified Data.Vector.Mutable as MLifted

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
  , fromIndexVar :: {-# unpack #-} !(GrowableVector MLifted.MVector s a)
  , nodesVar :: {-# unpack #-} !(GrowableVector MUnboxed.MVector s Node)
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
  | otherwise = go
  where
    go = fmap isJust $ runMaybeT $ do
      xRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d x)
      yRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d y)
      unless (xRoot == yRoot) $ do
        xRootSize <- size <$> indexToNode d xRoot
        yRootSize <- size <$> indexToNode d yRoot
        let nodes = nodesVar d
        when (xRootSize < yRootSize) (swap nodes xRoot yRoot)
        modify nodes (\n -> n { parent = xRoot }) yRoot
        modify nodes (\n -> n { size = xRootSize + yRootSize }) xRoot
{-# inline union #-}

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
  deriving anyclass (Unbox)

data instance Base.MVector s Node
  = MV_2 {-# unpack #-} !Int
                        !(MUnboxed.MVector s Index)
                        !(MUnboxed.MVector s Int)

data instance Base.Vector Node
  = V_2 {-# unpack #-} !Int
                       !(Unboxed.Vector Index)
                       !(Unboxed.Vector Int)

instance MClass.MVector MUnboxed.MVector Node where
  basicLength (MV_2 n _ _) = n
  {-# inline basicLength #-}
  basicUnsafeSlice i m (MV_2 _ parents sizes)
    = MV_2 m (MClass.basicUnsafeSlice i m parents)
             (MClass.basicUnsafeSlice i m sizes)
  {-# inline basicUnsafeSlice #-}
  basicOverlaps (MV_2 _ parents0 sizes0) (MV_2 _ parents1 sizes1)
    = MClass.basicOverlaps parents0 parents1
      || MClass.basicOverlaps sizes0 sizes1
  {-# inline basicOverlaps #-}
  basicUnsafeNew n = do
    parents <- MClass.basicUnsafeNew n
    sizes <- MClass.basicUnsafeNew n
    pure (MV_2 n parents sizes)
  {-# inline basicUnsafeNew #-}
  basicInitialize (MV_2 _ parents sizes) = do
    MClass.basicInitialize parents
    MClass.basicInitialize sizes
  {-# inline basicInitialize #-}
  basicUnsafeReplicate n (Node parent size) = do
    parents <- MClass.basicUnsafeReplicate n parent
    sizes <- MClass.basicUnsafeReplicate n size
    pure (MV_2 n parents sizes)
  {-# inline basicUnsafeReplicate #-}
  basicUnsafeRead (MV_2 _ parents sizes) i = do
    parent <- MClass.basicUnsafeRead parents i
    size <- MClass.basicUnsafeRead sizes i
    pure (Node parent size)
  {-# inline basicUnsafeRead #-}
  basicUnsafeWrite (MV_2 _ parents sizes) i (Node parent size) = do
    MClass.basicUnsafeWrite parents i parent
    MClass.basicUnsafeWrite sizes i size
  {-# inline basicUnsafeWrite #-}
  basicClear (MV_2 _ parents sizes) = do
    MClass.basicClear parents
    MClass.basicClear sizes
  {-# inline basicClear #-}
  basicUnsafeCopy (MV_2 _ parents0 sizes0) (MV_2 _ parents1 sizes1) = do
    MClass.basicUnsafeCopy parents0 parents1
    MClass.basicUnsafeCopy sizes0 sizes1
  {-# inline basicUnsafeCopy #-}
  basicUnsafeMove (MV_2 _ parents0 sizes0) (MV_2 _ parents1 sizes1) = do
    MClass.basicUnsafeMove parents0 parents1
    MClass.basicUnsafeMove sizes0 sizes1
  {-# inline basicUnsafeMove #-}
  basicUnsafeGrow (MV_2 n parents sizes) m = do
    parents' <- MClass.basicUnsafeGrow parents m
    sizes' <- MClass.basicUnsafeGrow sizes m
    pure (MV_2 (m + n) parents' sizes')
  {-# inline basicUnsafeGrow #-}

instance VClass.Vector Unboxed.Vector Node where
  basicUnsafeFreeze (MV_2 n parents sizes) = do
    parents' <- VClass.basicUnsafeFreeze parents
    sizes' <- VClass.basicUnsafeFreeze sizes
    pure (V_2 n parents' sizes')
  {-# inline basicUnsafeFreeze #-}
  basicUnsafeThaw (V_2 n parents sizes) = do
    parents' <- VClass.basicUnsafeThaw parents
    sizes' <- VClass.basicUnsafeThaw sizes
    pure (MV_2 n parents' sizes')
  {-# inline basicUnsafeThaw #-}
  basicLength (V_2 n _ _) = n
  {-# inline basicLength #-}
  basicUnsafeSlice i m (V_2 _ parents sizes)
    = V_2 m (VClass.basicUnsafeSlice i m parents)
            (VClass.basicUnsafeSlice i m sizes)
  {-# inline basicUnsafeSlice #-}
  basicUnsafeIndexM (V_2 _ parents sizes) i = do
    parent <- VClass.basicUnsafeIndexM parents i
    size <- VClass.basicUnsafeIndexM sizes i
    pure (Node parent size)
  {-# inline basicUnsafeIndexM #-}
  basicUnsafeCopy (MV_2 _ parents_mut sizes_mut) (V_2 _ parents sizes) = do
    VClass.basicUnsafeCopy parents_mut parents
    VClass.basicUnsafeCopy sizes_mut sizes
  {-# inline basicUnsafeCopy #-}

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

data GrowableVector v s a = GrowableVector
  { sizeVar :: {-# unpack #-} !(MutVar s Int)
  , vectorVar :: {-# unpack #-} !(MutVar s (v s a))
  }

sizeOf :: (MClass.MVector v a, PrimMonad m) => GrowableVector v (PrimState m) a -> m Int
sizeOf g = readMutVar (sizeVar g)

newGrowableVector :: (MClass.MVector v a, PrimMonad m) => Int -> m (GrowableVector v (PrimState m) a)
newGrowableVector sz = GrowableVector
  <$> newMutVar 0
  <*> (newMutVar =<< MClass.new sz)

read :: (MClass.MVector v a, PrimMonad m) => Int -> GrowableVector v (PrimState m) a -> m a
read n g = flip MClass.read n =<< readMutVar (vectorVar g)

readMaybe :: (MClass.MVector v a, PrimMonad m) => Int -> GrowableVector v (PrimState m) a -> m (Maybe a)
readMaybe n g = do
  sz <- sizeOf g
  if (n > 0 && n < sz)
    then Just <$> read n g
    else pure Nothing

push :: (MClass.MVector v a, PrimMonad m) => a -> GrowableVector v (PrimState m) a -> m ()
push x g = do
  needsResizing <- atMaxCapacity g
  when needsResizing (resize g)

  index <- readMutVar (sizeVar g)
  readMutVar (vectorVar g) >>= \v -> MClass.write v index x

  modifyMutVar' (sizeVar g) (+ 1)

-- We always resize by a factor of 2
resize :: (MClass.MVector v a, PrimMonad m) => GrowableVector v (PrimState m) a -> m ()
resize (GrowableVector sizeVar var) = do
  v <- readMutVar var
  v' <- MClass.unsafeGrow v (MClass.length v)
  writeMutVar var v'

-- Are we at max capacity?
atMaxCapacity :: (MClass.MVector v a, PrimMonad m)
  => GrowableVector v (PrimState m) a
  -> m Bool
atMaxCapacity g = go <$> readMutVar (sizeVar g) <*> (MClass.length <$> readMutVar (vectorVar g))
  where
    go x y = x + 1 >= y

modify :: (PrimMonad m, MClass.MVector v a)
  => GrowableVector v (PrimState m) a
  -> (a -> a)
  -> Int
  -> m ()
modify g f ix = readMutVar (vectorVar g) >>= \v -> MClass.modify v f ix

swap :: (PrimMonad m, MClass.MVector v a)
  => GrowableVector v (PrimState m) a
  -> Int
  -> Int
  -> m ()
swap g x y = readMutVar (vectorVar g) >>= \v -> MClass.swap v x y
