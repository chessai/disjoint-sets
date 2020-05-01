{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}

module Main
  ( main
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.ST
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import qualified Data.List.NonEmpty as NonEmpty

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import UnionFind (UnionFind)
import qualified UnionFind

main :: IO Bool
main = do
  checkSequential $$(discover)

prop_AllGood :: Property
prop_AllGood = property $ do
  groups <- forAll $ genEquivalenceClass
  let e = runST $ runExceptT $ do
        u <- equivalenceRelationToUnionFind groups
        checkUnionFind u groups
  case e of
    Right _ -> success
    Left err -> do
      footnote err
      failure

genEquivalenceClass :: forall m. MonadGen m => m [NonEmpty Int]
genEquivalenceClass = do
  sz <- Gen.int (Range.linear 3 10)
  let go :: Int -> [NonEmpty Int] -> StateT Int m [NonEmpty Int]
      go !currentGroup !acc = if currentGroup < sz
        then do
          len <- Gen.int (Range.linear 1 7)
          group <- forM [0..len] $ \_ -> do
            i <- get
            modify (+ 1)
            pure i
          go (currentGroup + 1) (NonEmpty.fromList group : acc)
        else do
          pure acc
  flip evalStateT 0 (go 0 [])

allEqual :: Eq a => NonEmpty a -> Bool
allEqual (a :| as) = all (== a) as

maybeToError :: MonadError e m => e -> Maybe a -> m a
maybeToError e = maybe (throwError e) pure

boolToError :: MonadError e m => e -> Bool -> m ()
boolToError e b = if b then pure () else throwError e

equivalenceRelationToUnionFind :: Ord a => [NonEmpty a] -> ExceptT String (ST s) (UnionFind s a)
equivalenceRelationToUnionFind groups = do
  u <- UnionFind.empty
  forM_ groups $ \group -> do
    forM_ group $ \element -> do
      UnionFind.insert u element
  forM_ groups $ \group -> do
    boolToError "unions failed!" =<< UnionFind.unions u (NonEmpty.toList group)
  pure u

checkUnionFind :: Ord a => UnionFind s a -> [NonEmpty a] -> ExceptT String (ST s) ()
checkUnionFind u groups = do
  forM_ groups $ \group -> do
    roots <- forM group $ \element -> do
      root <- maybeToError "find failed" =<< UnionFind.find u element
      unless (root `elem` group) $ do
        throwError "root was not an element of the group"
      pure root
    unless (allEqual roots) $ do
      throwError "roots not all equal"