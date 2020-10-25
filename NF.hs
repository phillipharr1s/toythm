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

nf' e = nf ([] :- e)

nf (c :- e) = case e of
  a :@ b -> case nf (c :- a) of
    Binder _ _ f -> nf (c :- op f b)
    otherwise -> a :@ nf (c :- b)
  _ :\ (f :@ B 0) | op (K 0) f == f -> f
  Binder (n :. a) x _ -> inBinder nf (c :- e)
  e -> e
