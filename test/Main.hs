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

import DisjointSets (DisjointSets)
import qualified DisjointSets

main :: IO Bool
main = do
  checkSequential $$(discover)

prop_union_find :: Property
prop_union_find = property $ do
  groups <- forAll $ genEquivalenceClasses
  let e = runST $ runExceptT $ do
        u <- equivalenceRelationToDisjointSets groups
        checkDisjointSets u groups
  case e of
    Right _ -> do
      success
    Left err -> do
      footnote err
      failure

genEquivalenceClasses :: forall m. MonadGen m => m [NonEmpty Int]
genEquivalenceClasses = do
  sz <- Gen.int (Range.linear 3 10)
  let go :: Int -> [NonEmpty Int] -> StateT Int m [NonEmpty Int]
      go !currentGroup !acc = if currentGroup < sz
        then do
          len <- Gen.int (Range.linear 4 20)
          group <- forM [0..len] $ \_ -> do
            i <- get
            modify (+ 1)
            pure i
          go (currentGroup + 1) (NonEmpty.fromList group : acc)
        else do
          pure acc
  flip evalStateT 0 (go 0 [])

equivalenceRelationToDisjointSets :: Ord a
  => [NonEmpty a]
  -> ExceptT String (ST s) (DisjointSets s a)
equivalenceRelationToDisjointSets groups = do
  u <- DisjointSets.empty
  forM_ groups $ \group -> do
    forM_ group $ \element -> do
      DisjointSets.insert u element
  forM_ groups $ \group -> do
    boolToError "unions failed!" =<< DisjointSets.unions u (NonEmpty.toList group)
  pure u

checkDisjointSets :: Ord a
  => DisjointSets s a
  -> [NonEmpty a]
  -> ExceptT String (ST s) ()
checkDisjointSets u groups = do
  forM_ groups $ \group -> do
    roots <- forM group $ \element -> do
      root <- maybeToError "find failed" =<< DisjointSets.find u element
      pure root

    -- is the root the same in all cases?
    unless (allEqual roots) $ do
      throwError "roots not all equal"

    -- is the root an element of the group?
    --
    -- note that this should should come after the allEqual check
    -- due to the use of 'NonEmpty.head'.
    unless (NonEmpty.head roots `within` group) $ do
      throwError "the minimal element returned by `find` is not an element of the group."

    -- is the root the minimal element?
    --
    -- note that this should should come after the allEqual check
    -- due to the use of 'NonEmpty.head'.
    unless (NonEmpty.head roots `isMinimalElementOf` group) $ do
      throwError "root is not the minimal element"

allEqual :: Eq a => NonEmpty a -> Bool
allEqual (a :| as) = all (== a) as

isMinimalElementOf :: Ord a => a -> NonEmpty a -> Bool
a `isMinimalElementOf` as = all (>= a) as

within :: Eq a => a -> NonEmpty a -> Bool
within a as = any (== a) as

maybeToError :: MonadError e m => e -> Maybe a -> m a
maybeToError e = maybe (throwError e) pure

boolToError :: MonadError e m => e -> Bool -> m ()
boolToError e b = if b then pure () else throwError e
