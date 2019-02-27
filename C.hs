{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}


module C where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Arrow

import Debug.Trace

import E

ix l n = l !! (n `mod` length l)

lk l n = typ $ ix l n

data C a = [B] :- a deriving(Eq, Ord, Functor, Foldable, Traversable, Show)

infixl 2 :-

f ==< (c :- e) = c :- (f $ c :- e)

l (c :- e) = (c :-) <$> e

ex (c :- e) = e

op' (c :- Binder a x b) = 
  a : c :- b `op` B (-length c)

cl' x (a : c :- b) =
  c :- Binder a x (b `cl` B (-length c))

opApp e@(c :- a :@ b) = Just (c :- a, c :- b)
opApp _ = Nothing

opLam e@(c :- n :. a :\ b) = Just (c :- a, op' e)
opLam _ = Nothing

opPi e@(c :- n :. a :> b) = Just (c :- a, op' e)
opPi _ = Nothing

pattern a :@! b <- (opApp -> Just (a, b))

pattern a :\! b <- (opLam -> Just (a, b))

pattern a :>! b <- (opLam -> Just (a, b))

