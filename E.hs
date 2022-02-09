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
infixr 4 :<

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

nf = \case
  (nf -> a :< _) :@ (nf -> b) -> nf (open a b)
  a :< n :. b -> nf a :< n :. nf b
  e -> e

expandTLDs :: E -> E
expandTLDs e = go (e :- []) where
  go (e@(a :< _) :@ b :- c) = open e''' b where
    e' :- c' = push (e :- c)
    e'' = go (e' :- c')
    e''' :- _ = pop (e'' :- c')
  go (a :@ b :- c) = go (a :- c) :@ go (b :- c)
  go (a :< n :. t :- c) = go (a :- n :. t : c) :< n :. go (t :- c)
  go (e :- c) = e

infixl 2 :-
data C a = a :- [B]
  deriving(Show)

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
  deriving(Show)

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

eq = "(= : #(x:A)(y:A)(A:#))"
refl = "(refl : [= X x x](x:X)(X:#))"
indEq = "(ind= : [P x y =xy](=xy : = A x y)(y:A)(x:A)(p : [P x x [refl A x]](x:A)) (P : #(-: = A x y)(y:A)(x:A) ) (A:#) )"

-- "#(pImpliesDnp : [dn P](p:P))[ [notP p]  (notP : not P)(p:P) ](P:#)(dn : #(Q:#))[[not [not Q]](Q:#)](not : #(-:#))[[false(a:A)](A:#)](false : #)[A(A:#)]"

-- tc :: [B] -> E -> Either TypeError E
-- tc c (a :< n :. t) = do
--   tc c t
--   ta <- tc (n :. t : c) (open a (F $ length c))
--   pure (ta :< n :. t)
-- tc c (a :@ b) = do
--   ta <- tc c a
--   tb <- tc c b
--   case (ta, tb) of
--     (_ :< n :. t, _) | unify t tb ->
--       pure $ nf (ta :@ b)
--     _ -> Left (CantUnify ta tb)
-- tc c (F k) = case ix c k of
--   _ :. t -> pure t
-- tc c (B k) = case c !! k of
--   _ :. t -> pure t
-- tc c (K k) = pure (K $ k+1)

-- parseExpr s = case parse expr "" s of Right e -> e

-- op e t = go 0 e where
--   go i e | e == t = B i
--   go i (a :@ b) = go i a :@ go i b


--
-- data C a
--  = [B] :- a
--


-- splitApp e = (a, reverse bs) where
--   (a, bs) = go e
--   go = \case
--     a :@ b -> (h, b : cs) where (h, cs) = go a
--     e -> (e, [])
--
-- instance Eq (B -> E -> E) where
--   x == y =
--     x ("" :. B 0) (B 0)
--     ==
--     y ("" :. B 0) (B 0)

-- splitBinder x = \case
--   Binder a x' b | x == x' -> (h, a : cs)
--     where (h, cs) = splitBinder x b
--   e -> (e, [])
--
-- splitLam = splitBinder (:\)
--
-- splitPi = splitBinder (:>)

-- pattern a :@@ bs <- (splitApp -> (a, bs))
--   where a :@@ bs = foldl (:@) a bs
--
-- pattern (:\\) :: [B] -> E -> E
-- pattern as :\\ b <- (splitLam -> (b, as))
--   where as :\\ b = foldr (:\) b as
--
-- pattern (:>>) :: [B] -> E -> E
-- pattern as :>> b <- (splitPi -> (b, as))
--   where as :>> b = foldr (:>) b as

-- pattern a :@: b = a :@ b
--
-- pattern a :\: b <- _ :. a :\ b
--   where a :\: b = "" :. a :\ b
--
-- pattern a :>: b <- _ :. a :> b
--   where a :>: b = "" :. a :> b

-- r f g = \case
--   Binder (n :. a) x b -> (n :. f a) `x` g b
--   a :@ b -> f a :@ f b
--   e -> e
--
-- r' f = r f f
--
-- rb f n = r (f n) (f $ n + 1)
--
-- op e t = go 0 e where
--   go i = \case
--     e | e == B i -> t
--       | otherwise -> rb go i e
--
-- cl e t = go 0 e where
--   go i = \case
--     e | e == t -> B i
--       | otherwise -> rb go i e
