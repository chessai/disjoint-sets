{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}

module UnionFind
  ( UnionFind
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

data UnionFind s a = UnionFind
  { sizeVar :: {-# UNPACK #-} !(MutVar s Int)
  , toIndexVar :: {-# UNPACK #-} !(MutVar s (Map a Index))
  , fromIndexVar :: {-# UNPACK #-} !(MutVar s (Map Index a))
  , nodesVar :: {-# UNPACK #-} !(MutVar s (MVector s Node))
  }

data Node = Node
  { parent :: Index
  , size :: Int
  }

empty :: (PrimMonad m) => m (UnionFind (PrimState m) a)
empty = UnionFind
  <$> newMutVar 0
  <*> newMutVar Map.empty
  <*> newMutVar Map.empty
  <*> (newMutVar =<< MVector.new 1)

atMaxCapacity :: PrimMonad m => UnionFind (PrimState m) a -> m Bool
atMaxCapacity u = go <$> readMutVar (sizeVar u) <*> (MVector.length <$> getNodes u)
  where
    go x y = x + 1 >= y

resize :: PrimMonad m => UnionFind (PrimState m) a -> m ()
resize u = do
  nodes <- getNodes u
  nodes' <- MVector.unsafeGrow nodes (MVector.length nodes)
  writeMutVar (nodesVar u) nodes'

insert :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> a -> m ()
insert u a = do
  needsResizing <- atMaxCapacity u
  when needsResizing $ do
    resize u

  index <- readMutVar (sizeVar u)
  modifyMutVar' (toIndexVar u) (Map.insert a index)
  modifyMutVar' (fromIndexVar u) (Map.insert index a)
  readMutVar (nodesVar u) >>= \v -> MVector.write v index (Node { parent = index, size = 1 })

  modifyMutVar' (sizeVar u) (+1)

getNodes :: (PrimMonad m) => UnionFind (PrimState m) a -> m (MVector (PrimState m) Node)
getNodes u = readMutVar (nodesVar u)

getIndex :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> a -> m (Maybe Index)
getIndex UnionFind{toIndexVar} a = Map.lookup a <$> readMutVar toIndexVar

getNode :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> a -> m (Maybe Node)
getNode u x = do
  mindex <- getIndex u x
  forM mindex $ \index -> indexToNode u index

indexToNode :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> Index -> m Node
indexToNode u ix = flip MVector.read ix =<< getNodes u

indexToValue :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> Index -> m (Maybe a)
indexToValue UnionFind{fromIndexVar} ix = Map.lookup ix <$> readMutVar fromIndexVar

findIndex :: forall m a. (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> Index -> m (Maybe Index)
findIndex u ix = runMaybeT $ do
  let go :: Index -> MaybeT m Index
      go !x = do
        p <- parent <$> indexToNode u x
        pp <- parent <$> indexToNode u p
        if (p /= x)
          then do
            nodes <- getNodes u
            MVector.modify nodes (\n -> n { parent = pp }) p
            go p
          else do
            pure x
  go ix

find :: forall m a. (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> a -> m (Maybe a)
find u a = runMaybeT $ do
  ix <- (MaybeT . findIndex u) =<< MaybeT (getIndex u a)
  MaybeT (indexToValue u ix)

union :: forall m a. (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> a -> a -> m Bool
union u x y = fmap isJust $ runMaybeT $ do
  xRoot <- (MaybeT . findIndex u) =<< MaybeT (getIndex u x)
  yRoot <- (MaybeT . findIndex u) =<< MaybeT (getIndex u y)
  if xRoot == yRoot
    then do
      pure ()
    else do
      Node{size=xRootSize} <- indexToNode u xRoot
      Node{size=yRootSize} <- indexToNode u yRoot
      nodes <- getNodes u
      when (xRootSize < yRootSize) $ do
        MVector.swap nodes xRoot yRoot
      MVector.modify nodes (\n -> n { parent = xRoot }) yRoot
      MVector.modify nodes (\n -> n { size = xRootSize + yRootSize }) xRoot

unions :: (PrimMonad m, Ord a) => UnionFind (PrimState m) a -> [a] -> m Bool
unions u = fmap and . go
  where
    go = \case
      [] -> pure [True]
      [_] -> pure [True]
      (x:xs) -> forM xs $ \a -> union u x a

