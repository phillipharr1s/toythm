{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module T where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import E
import C
import NF

import System.Timeout

import Debug.Trace

genM :: [N] -> Gen E
genM [] = genK
genM ns = Gen.element $ map M ns

genK :: Gen E
genK = Gen.frequency 
  [ (9, pure $ K 0)
  , (2, pure $ K 1)
  , (1, pure $ K 2)
  ]

genB :: I -> Gen E
genB 0 = genK
genB i = Gen.element $ map B [0..i-1]

genApp :: I -> Gen E
genApp i = Gen.subterm2 (genExpr i) (genExpr i) (:@)

genLam :: I -> Gen E
genLam i = Gen.subterm2 (genExpr i) (genExpr $ i + 1) (\a b -> "" :. a :\ b)

genPi :: I -> Gen E
genPi i = Gen.subterm2 (genExpr i) (genExpr $ i + 1) (\a b -> "" :. a :> b)

genExpr :: I -> Gen E
genExpr i = Gen.recursive Gen.choice
  [ genM []
  , genK
  , genB i
  ]
  [ genApp i
  , genLam i
  , genPi  i
  ]

good e = go 0 e where
  go i (B j) = j < i
  go i (a :@ b) = go i a && go i b
  go i (Binder (_ :. a) _ b) = go i a && go (i+1) b
  go i _ = True

untypedId = "" :. T :\ B 0

checkEquivNF a b = do
  ans <- timeout 100 (pure $ nf' a == nf' b)
  pure $ ans == Just True

prop_good :: Property
prop_good = property $ do
  e <- forAll (genExpr 0)
  assert (good e)

prop_nf :: Property
prop_nf = withShrinks 0 $ property $ do
  e <- forAll (genExpr 0)
  assert (good $ nf' e)

prop_Id :: Property
prop_Id = property $ do
  e <- forAll (genExpr 0)
  assert =<< (evalIO $ checkEquivNF (nf' $ untypedId :@ e) e)

namedId = "A" :. K 0 :\ "a" :. M "A" :\ M "a"
unNamedId = "A" :. K 0 :\ "a" :. B 0 :\ B 0

prop_fromNamed_Id :: Property
prop_fromNamed_Id = property $ fromNamed namedId === unNamedId

tests :: IO Bool
tests =
  checkParallel $$(discover)