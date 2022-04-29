{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module E where

import Prelude hiding (drop)
import Data.List hiding (drop)
import Data.Maybe
import Data.Function
import Control.Monad
import Control.Arrow

import Debug.Trace

import Text.Parsec
import Text.Parsec.Char

import qualified Control.Exception

import           Test.Tasty.Hedgehog
import           Test.Tasty

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import System.Timeout

import Debug.Trace

spy x = trace (show x) x

fromRight (Right x) = x
fromRight (Left x) = error (show x)

type N = String

type I = Int

data B = N :. E
  deriving (Show, Ord)

infixl 6 :.

instance Eq B where
  (_ :. a) == (_ :. b) =
    a == b

nam (n :. e) = n
typ (n :. e) = e

infixl 4 :@
infixl 4 :<

data E
 = M N
 | K I
 | B I
 | F I
 | E :@ E
 | E :< B
 deriving (Show, Eq, Ord)

pattern P = K 0
pattern T = K 1

r f i = \case
  a :< n :. b -> f (i+1) a :< n :. f i b
  a :@ b -> f i a :@ f i b
  e -> e

open e t = go 0 e where
  go i = \case
    e | e == B i -> t
    e -> r go i e

close e t = go 0 e where
  go i = \case
    e | e == t -> B i
    e -> r go i e

nf = go 0 where 
  go i = \case 
    (go i -> a :< _) :@ (go i -> b) -> go i (open a b)
    a :< n :. b -> close (go (i+1) (open a (F i))) (F i) :< n :. go i b
    e -> e

infixl 2 :-
data C a = a :- [B]
  deriving(Show, Eq)

push :: C E -> C E
push (a :< n :. t :- c) = open a (F $ length c) :- (n :. t : c)
push e = e

pop :: C E -> C E
pop (a :- n :. t : c) = close a (F $ length c) :< n :. t :- c
pop e = e

drop (a :- c) = a

keep f (e :- c) = f (e :- c) :- c

ix c k = reverse c !! k

type Parse a = Parsec String () a

parseName :: Parse N
parseName = many1 (oneOf "<>?!@#$%^&*-=_+{}/\\" <|> letter <|> digit)

parseVar :: Parse E
parseVar = spaces >> (M <$> parseName)

inParens :: Parse a -> Parse a
inParens = between (char '(') (spaces >> char ')')

inBrackets :: Parse a -> Parse a
inBrackets = between (char '[') (spaces >> char ']')

parseBind :: Parse B
parseBind = inParens $ do
  M n <- parseVar
  spaces >> char ':'
  b <- parseExpr
  return (n :. b)

parseApp :: Parse E
parseApp = (spaces >>) $
  parseVar <|> (foldl1 (:@) <$> inBrackets (many1 parseExpr))

parseBlock :: Parse (Either B E)
parseBlock = (spaces >>) $
      (Left <$> parseBind)
  <|> (Right <$> inBrackets parseExpr)
  <|> (Right <$> parseVar)

parseExpr :: Parse E
parseExpr = spaces >> do
  Right firstBlock <- parseBlock
  rest <- many (try parseBlock)
  return (go firstBlock rest)
    where
      go e (Left b : xs) = go (e :< b) xs
      go e (Right f : xs) = go (e :@ f) xs
      go e [] = e

p = fromNamed [] . fromRight . parse parseExpr ""

weight :: E -> Int
weight (_ :@ _) = 3
weight (_ :< _) = 2
weight _ = 1

addBrackets e =
  if weight e > 2
    then "[" ++ pretty e ++ "]"
    else pretty e

pretty (a :@ b) = pretty a ++ " " ++ addBrackets b
pretty (a :< n :. t) =
  addBrackets a ++ "(" ++ n ++ colon ++ pretty t ++ ")"
    where colon = if weight t > 1 then " : " else ":"

pretty (M n) = n
pretty (F k) = "." ++ show k
pretty (B k) = "|" ++ show k
pretty (K k) = take (k+1) (repeat '#')

lookupName c n = go 0 c n where
  go k (m :. _ : xs) n | n == m = k
  go k (_ : xs) n = go (k+1) xs n
  go k [] _ = -1

class ConvertNames a where
  fromNamed :: [B] -> a -> a
  toNamed :: [B] -> a -> a

instance ConvertNames E where
  fromNamed c (a :@ b) =
    fromNamed c a :@ fromNamed c b
  fromNamed c (a :< n :. t) =
    fromNamed (n :. t : c) a :< n :. fromNamed c t
  fromNamed c (M "#") = K 0
  fromNamed c (M n) = case lookupName c n of
    -1 -> M n
    k -> B k
  fromNamed c e = e

  toNamed c (a :@ b) =
    toNamed c a :@ toNamed c b
  toNamed c (a :< n :. t) =
    toNamed (n :. t : c) a :< n :. toNamed c t
  toNamed c (B k) = case c!!k of
    n :. t -> M n
  toNamed c (F k) = case ix c k of
    n :. t -> M n
  toNamed c e = e

test = pretty . toNamed [] . drop . fromRight . tc . (:- []) . p

data TypeError = CantUnify E E E E
  deriving(Show, Eq)

instance ConvertNames TypeError where
  fromNamed c (CantUnify a b ta tb) =
    CantUnify
      (fromNamed c a)
      (fromNamed c b)
      (fromNamed c ta)
      (fromNamed c tb)
  toNamed c (CantUnify a b ta tb) =
    CantUnify
      (toNamed c a)
      (toNamed c b)
      (toNamed c ta)
      (toNamed c tb)

unify :: E -> E -> Bool
unify a b = go (nf a) (nf b) where
  go (K k) (a :< _) = go (K k) a
  go (a :< _) (K k) = go a (K k)
  go (a :< _ :. t) (a' :< _ :. t') = go a a' && go t t'
  go (a :@ b) (a' :@ b') = go a a' && go b b'
  go (B k) (B k') = (k == k')
  go (F k) (F k') = (k == k')
  go (K k) (K k') = (k == k')
  go (M n) (M n') = (n == n')
  go _ _ = False

tc :: C E -> Either (C TypeError) (C E)
tc e@(a :< n :. t :- c) = do
  tc (t :- c)
  ta <- tc (push e)
  pure $ pop ta
tc (a :@ b :- c) = do
  (nf -> ta) :- _ <- tc (a :- c)
  (nf -> tb) :- _ <- tc (b :- c)
  case (ta, tb) of
    (_ :< n :. t, tb) | unify t tb ->
      pure $ nf (ta :@ b) :- c
    _ -> Left (toNamed c (CantUnify a b ta tb) :- c)
tc (F k :- c) = case ix c k of
  _ :. t -> pure (t :- c)
tc (K k :- c) = pure $ K (k+1) :- c
tc (M n :- c) = error $ "out of scope? " ++ n
tc e = trace (show e) undefined

tc' :: C E -> E
tc' e = t where Right (t :- _) = tc e

eq = "(= : #(x:A)(y:A)(A:#))"
refl = "(refl : [= X x x](x:X)(X:#))"
indEq = "(ind= : [P x y =xy](=xy : = A x y)(y:A)(x:A)(p : [P x x [refl A x]](x:A)) (P : #(-: = A x y)(y:A)(x:A) ) (A:#) )"

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

genBinder i = do
  a <- genExpr i
  b <- genExpr (i + 1)
  n <- genN
  pure $ b :< n :. a

genExpr :: I -> Gen E
genExpr i = Gen.recursive Gen.choice
  [ genM []
  , genK
  , genB i
  ]
  [ genApp i
  , genBinder i
  ]

respectsBindLevel e = go 0 e where
  go i (B j) = j < i
  go i (a :@ b) = go i a && go i b
  go i (b :< (_ :. a)) = go i a && go (i+1) b
  go i _ = True

untypedId = B 0 :< "" :. T 

checkEquivNF a b = do
  ans <- timeout 12345 (pure $ nf a == nf b)
  pure $ ans == Just True

prop_good :: Property
prop_good = property $ do
  e <- forAll (genExpr 0)
  assert (respectsBindLevel e)

prop_nf :: Property
prop_nf = withShrinks 0 $ property $ do
  e <- forAll (genExpr 0)
  assert (respectsBindLevel e)
  assert (respectsBindLevel $ nf e)

prop_named_nf :: Property
prop_named_nf = property $ do
  e <- forAll (genExpr 0)
  assert $ toNamed [] e == (toNamed [] . fromNamed [] . toNamed []) e
  --the simpler version does not quite hold
  --because the genN's aren't unique

prop_fromNamed_Id :: Property
prop_fromNamed_Id = property $ fromNamed [] namedId === unNamedId


prop_Id :: Property
prop_Id = property $ do
  e <- forAll (genExpr 0)
  assert =<< (evalIO $ checkEquivNF (nf $ untypedId :@ e) e)


prop_Eqn :: (E, E) -> Property
prop_Eqn (e1, e2) = property $
  assert =<< (evalIO $ checkEquivNF e1 e2)

prop_tcK :: Property
prop_tcK = property $ do
  i <- forAll $ Gen.integral (Range.constantFrom 0 1 3)
  assert $ tc (K i :- []) == Right (K (i+1) :- [])

prop_tcId :: Property
prop_tcId = property $ do
  assert $ tc' (fromNamed [] namedId :- []) == fromNamed [] namedIdType

prop_tcFalse :: Property
prop_tcFalse = property $ do
  assert $ tc' (fromNamed [] namedFalse :- []) == (K 0)

prop_tcFalseImpliesTrue :: Property
prop_tcFalseImpliesTrue = property $ do
  assert $ tc' (fromNamed [] namedFalseImpliesTruePf :- []) == fromNamed [] namedFalseImpliesTrue

namedId = M "a" :< "a" :. M "A" :< "A" :. K 0
namedIdType = M "A" :< "a" :. M "A" :< "A" :. K 0
unNamedId = B 0 :< "a" :. B 0 :< "A" :. K 0 

namedFalse = M "A" :< "A" :. K 0
namedTrue = namedIdType

namedFalseImpliesTruePf = 
  (M "p" :@ namedTrue) :< "p" :. namedFalse
namedFalseImpliesTrue =
  namedTrue :< "p" :. namedFalse 

go = defaultMain allTests

allTests = testGroup "all"
  [ genIsSound
  -- , goodConcreteEqns
  -- , goodParamEqns
  -- , goodTC
  -- , badTC
  -- , parsePrint
  ]

goodTC = testGroup "good typecheck" $
  map (testProperty "")
  [ prop_tcK
  , prop_tcFalse
  , prop_tcId
  , prop_tcFalseImpliesTrue
  -- , prop_tcRing
  ]

genIsSound = testGroup "basic sanity checks for gen" $
  map (testProperty "")
  [ prop_good
  , prop_nf
  , prop_named_nf
  -- , prop_fromNamed_Id
  ]



-- "#(pImpliesDnp : [dn P](p:P))[ [notP p]  (notP : not P)(p:P) ](P:#)(dn : #(Q:#))[[not [not Q]](Q:#)](not : #(-:#))[[false(a:A)](A:#)](false : #)[A(A:#)]"
