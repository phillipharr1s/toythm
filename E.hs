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

import Data.List
import Data.Maybe
import Data.Function
import Control.Monad
import Control.Arrow

import Debug.Trace

spy x = trace (show x) x

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

data E
 = M N
 | K I
 | B I
 | F I
 | E :@ E
 | B :\ E
 | B :> E
 deriving (Show, Eq, Ord)

infixl 4 :@
infixr 3 :\
infixr 3 :>

pattern P = K 0
pattern T = K 1

asBinder = \case
  a :\ b -> Just $ (a, (:\), b)
  a :> b -> Just $ (a, (:>), b)
  _ -> Nothing

pattern Binder a x b <- (asBinder -> Just (a, x, b))
  where Binder a x b = x a b

splitApp = second reverse . go where
  go = \case
    a :@ b -> (h, b : cs) where (h, cs) = go a
    e -> (e, [])

instance Eq (B -> E -> E) where
  x == y =
    x ("" :. B 0) (B 0)
    ==
    y ("" :. B 0) (B 0)

splitBinder x = \case
  Binder a x' b | x == x' -> (h, a : cs)
    where (h, cs) = splitBinder x b
  e -> (e, [])

splitLam = splitBinder (:\)

splitPi = splitBinder (:>)

pattern a :@@ bs <- (splitApp -> (a, bs))
  where a :@@ bs = foldl (:@) a bs

pattern (:\\) :: [B] -> E -> E
pattern as :\\ b <- (splitLam -> (b, as))
  where as :\\ b = foldr (:\) b as

pattern (:>>) :: [B] -> E -> E
pattern as :>> b <- (splitPi -> (b, as))
  where as :>> b = foldr (:>) b as

pattern a :@: b = a :@ b

pattern a :\: b <- _ :. a :\ b
  where a :\: b = "" :. a :\ b

pattern a :>: b <- _ :. a :> b
  where a :>: b = "" :. a :> b

r f g = \case
  Binder (n :. a) x b -> (n :. f a) `x` g b
  a :@ b -> f a :@ f b
  e -> e

r' f = r f f

rb f n = r (f n) (f $ n + 1)

op e t = go 0 e where
  go i = \case
    e | e == B i -> t
      | otherwise -> rb go i e

cl e t = go 0 e where
  go i = \case
    e | e == t -> B i
      | otherwise -> rb go i e
