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
{-# LANGUAGE OverloadedStrings #-}


module T where

import qualified Control.Exception

import           Test.Tasty.Hedgehog
import           Test.Tasty

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Either

import E
import C
import NF
import TT
import PP

import System.Timeout

import Debug.Trace

genN :: Gen N
genN = Gen.element $ map (:[]) $ ['a'..'z'] ++ ['A'..'Z']

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
genB 0 = genK -- ??? TODO: remove?
genB i = Gen.element $ map B [0..i-1]

genApp :: I -> Gen E
genApp i = Gen.subterm2 (genExpr i) (genExpr i) (:@)

genBinder x i = do
  a <- genExpr i
  b <- genExpr (i + 1)
  n <- genN
  pure $ (n :. a) `x` b

genLam :: I -> Gen E
genLam = genBinder (:\)

genPi :: I -> Gen E
genPi = genBinder (:>)

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

respectsBindLevel e = go 0 e where
  go i (B j) = j < i
  go i (a :@ b) = go i a && go i b
  go i (Binder (_ :. a) _ b) = go i a && go (i+1) b
  go i _ = True

untypedId = "" :. T :\ B 0

checkEquivNF a b = do
  ans <- timeout 12345 (pure $ nf' a == nf' b)
  pure $ ans == Just True

prop_good :: Property
prop_good = property $ do
  e <- forAll (genExpr 0)
  assert (respectsBindLevel e)

prop_nf :: Property
prop_nf = withShrinks 0 $ property $ do
  e <- forAll (genExpr 0)
  assert (respectsBindLevel $ nf' e)

prop_named_nf :: Property
prop_named_nf = property $ do
  e <- forAll (genExpr 0)
  assert $ toNamed e == (toNamed . fromNamed . toNamed) e
  --the simpler version does not quite hold
  --because the genN's aren't unique

prop_fromNamed_Id :: Property
prop_fromNamed_Id = property $ fromNamed namedId === unNamedId

prop_Id :: Property
prop_Id = property $ do
  e <- forAll (genExpr 0)
  assert =<< (evalIO $ checkEquivNF (nf' $ untypedId :@ e) e)

prop_Eqn :: (E, E) -> Property
prop_Eqn (e1, e2) = property $
  assert =<< (evalIO $ checkEquivNF e1 e2)

prop_tcK :: Property
prop_tcK = property $ do
  i <- forAll $ Gen.integral (Range.constantFrom 0 1 3)
  assert $ tc' ([] :- K i) == K (i+1)

prop_tcId :: Property
prop_tcId = property $ do
  assert $ tc' ([] :- fromNamed namedId) == fromNamed namedIdType

prop_tcFalse :: Property
prop_tcFalse = property $ do
  assert $ tc' ([] :- fromNamed namedFalse) == (K 0)

prop_tcFalseImpliesTrue :: Property
prop_tcFalseImpliesTrue = property $ do
  assert $ tc' ([] :- fromNamed namedFalseImpliesTruePf) == fromNamed namedFalseImpliesTrue

prop_tcRing :: Property
prop_tcRing = property $ do
  assert $ isRight (tc $ fromNamed eqTrans)

namedId = "A" :. K 0 :\ "a" :. M "A" :\ M "a"
namedIdType = "A" :. K 0 :> "a" :. M "A" :> M "A"
unNamedId = "A" :. K 0 :\ "a" :. B 0 :\ B 0

namedFalse = "A" :. K 0 :> M "A"

namedTrue = "A" :. K 0 :> "a" :. M "A" :> M "A"

namedFalseImpliesTruePf =
  "p" :. namedFalse :\ M "p" :@ namedTrue
namedFalseImpliesTrue =
  "p" :. namedFalse :> namedTrue

allTests = testGroup "all"
  [ genIsSound
  , goodConcreteEqns
  , goodParamEqns
  , goodTC
  , badTC
  , parsePrint
  ]

genIsSound = testGroup "basic sanity checks for gen" $
  map (testProperty "")
  [ prop_good
  , prop_nf
  , prop_named_nf
  , prop_fromNamed_Id
  ]

goodConcreteEqns = testGroup "concrete eqns" $
  map (testProperty "") $
  map prop_Eqn
  [ (i, i)
  , (i, i :@ ti :@ i)
  , (i, i :@ ti :@ (i :@ ti :@ i))
  , (i :@ ti :@ i, i :@ ti :@ i :@ ti :@ i)
  , (ui, ui)
  , (ui, ui :@ ui)
  , (ui, ui :@ (ui :@ ui))
  , (ui, ui :@ ui :@ ui)
  ]
  where i = unNamedId
        ti = fromNamed namedTrue
        ui = untypedId

goodParamEqns = testGroup "parameterized eqns" $
  map (testProperty "")
  [ prop_Id
  ]

goodTC = testGroup "good typecheck" $
  map (testProperty "")
  [ prop_tcK
  , prop_tcFalse
  , prop_tcId
  , prop_tcFalseImpliesTrue
  , prop_tcRing
  ]

parsePrint = testGroup "parse pretty print" $
  map (testProperty "")
  [ prop_print_parse
  ]

prop_print_parse :: Property
prop_print_parse = property $ do
  e <- forAll (genExpr 0)
  assert $ e == parseExpr (p e)

expectBadTC :: C E -> Property
expectBadTC ce = property $ do
  assert $ not $ isRight $ (tc ce)

badTC = testGroup "bad typecheck" $
  map (\e -> testProperty (show e) $ expectBadTC ([] :- e))
  [ K 0 :@ K 0
  , fromNamed $
  "A" :. K 0 :\ "a" :. M "A" :\ M "a" :@ M "a"
  ]

go = defaultMain allTests
