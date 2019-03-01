{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module NF where

import Data.List
import Data.Maybe
import Data.Function
import Control.Monad
import Control.Arrow

import Debug.Trace

import E
import C

-- nf = \case
--   (nf -> a) :@ (nf -> b) 
--    | Binder _ _ f <- a -> nf $ op b f
--    | otherwise -> a :@ b
--   _ :\ (f :@ B 0) | op (K 0) f == f -> f
--   Binder (n :. a) x b -> 
--     Binder (n :. nf a) x (nf b)
--   e -> r' nf e

-- nf (c :- e) = case e of
--   (nf -> a) :@ (nf -> b) 
--    | Binder _ _ f <- a -> nf (c :- op b f)
--    | otherwise -> a :@ b
--   _ :\ (f :@ B 0) | op (K 0) f == f -> f
--   Binder (n :. a) x b -> 
--     Binder (n :. nf a) x (nf b)
--   e -> e

nf' e = nf ([] :- e)

nf (c :- e) = case e of
  a :@ b -> case nf (c :- a) of
    Binder _ _ f -> nf (c :- op b f)
    otherwise -> a :@ nf (c :- b)
  _ :\ (f :@ B 0) | op (K 0) f == f -> f
  Binder (n :. a) x _ ->
    ex $ cl' x (nf ==< (op' $ c :- e))
  e -> e

-- newtype NF = NF E 

-- instance Eq NF where
--   (==) (NF a) (NF b) = case (a, b) of
--     (M a, M b) -> a == b
--     (K i, K j) -> i == j
--     (B i, B j) -> i == j
--     (a :@: b, a' :@: b') -> eq a b a' b'
--     (a :\: b, a' :\: b') -> eq a b a' b'
--     (a :>: b, a' :>: b') -> eq a b a' b'
--     _ -> False

-- eq a b a' b' = NF a == NF a' && NF b == NF b'

-- instance Eq E where
--   (==) = (==) `on` (NF . nf)