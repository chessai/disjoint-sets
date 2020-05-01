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

type Index = Int

data DisjointSets s a = DisjointSets
  { sizeVar :: {-# UNPACK #-} !(MutVar s Int)
  , toIndexVar :: {-# UNPACK #-} !(MutVar s (Map a Index))
  , fromIndexVar :: {-# UNPACK #-} !(MutVar s (Map Index a))
  , nodesVar :: {-# UNPACK #-} !(MutVar s (MVector s Node))
  }

data Node = Node
  { parent :: Index
  , size :: Int
  }

empty :: (PrimMonad m) => m (DisjointSets (PrimState m) a)
empty = DisjointSets
  <$> newMutVar 0
  <*> newMutVar Map.empty
  <*> newMutVar Map.empty
  <*> (newMutVar =<< MVector.new 1)

atMaxCapacity :: PrimMonad m => DisjointSets (PrimState m) a -> m Bool
atMaxCapacity d = go <$> readMutVar (sizeVar d) <*> (MVector.length <$> getNodes d)
  where
    go x y = x + 1 >= y

resize :: PrimMonad m => DisjointSets (PrimState m) a -> m ()
resize d = do
  nodes <- getNodes d
  nodes' <- MVector.unsafeGrow nodes (MVector.length nodes)
  writeMutVar (nodesVar d) nodes'

insert :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> a -> m ()
insert d a = do
  needsResizing <- atMaxCapacity d
  when needsResizing $ do
    resize d

  index <- readMutVar (sizeVar d)
  modifyMutVar' (toIndexVar d) (Map.insert a index)
  modifyMutVar' (fromIndexVar d) (Map.insert index a)
  readMutVar (nodesVar d) >>= \v -> MVector.write v index (Node { parent = index, size = 1 })

  modifyMutVar' (sizeVar d) (+1)

getNodes :: (PrimMonad m) => DisjointSets (PrimState m) a -> m (MVector (PrimState m) Node)
getNodes d = readMutVar (nodesVar d)

getIndex :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> a -> m (Maybe Index)
getIndex DisjointSets{toIndexVar} a = Map.lookup a <$> readMutVar toIndexVar

getNode :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> a -> m (Maybe Node)
getNode d x = do
  mindex <- getIndex d x
  forM mindex $ \index -> indexToNode d index

indexToNode :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> Index -> m Node
indexToNode d ix = flip MVector.read ix =<< getNodes d

indexToValue :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> Index -> m (Maybe a)
indexToValue DisjointSets{fromIndexVar} ix = Map.lookup ix <$> readMutVar fromIndexVar

findIndex :: forall m a. (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> Index -> m (Maybe Index)
findIndex d ix = runMaybeT $ do
  let go :: Index -> MaybeT m Index
      go !x = do
        p <- parent <$> indexToNode d x
        pp <- parent <$> indexToNode d p
        if (p /= x)
          then do
            nodes <- getNodes d
            MVector.modify nodes (\n -> n { parent = pp }) p
            go p
          else do
            pure x
  go ix

find :: forall m a. (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> a -> m (Maybe a)
find d a = runMaybeT $ do
  ix <- (MaybeT . findIndex d) =<< MaybeT (getIndex d a)
  MaybeT (indexToValue d ix)

union :: forall m a. (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> a -> a -> m Bool
union d x y = fmap isJust $ runMaybeT $ do
  xRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d x)
  yRoot <- (MaybeT . findIndex d) =<< MaybeT (getIndex d y)
  if xRoot == yRoot
    then do
      pure ()
    else do
      Node{size=xRootSize} <- indexToNode d xRoot
      Node{size=yRootSize} <- indexToNode d yRoot
      nodes <- getNodes d
      when (xRootSize < yRootSize) $ do
        MVector.swap nodes xRoot yRoot
      MVector.modify nodes (\n -> n { parent = xRoot }) yRoot
      MVector.modify nodes (\n -> n { size = xRootSize + yRootSize }) xRoot

unions :: (PrimMonad m, Ord a) => DisjointSets (PrimState m) a -> [a] -> m Bool
unions d = fmap and . go
  where
    go = \case
      [] -> pure [True]
      [_] -> pure [True]
      (x:xs) -> forM xs $ \a -> union d x a

