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

ix l n = reverse l !! n

lk l n = typ (ix l n)

data C a = [B] :- a deriving(Eq, Ord, Functor, Foldable, Traversable, Show)

infixl 2 :-

-- these are comonad functions
-- not worth using the libraries

f <<= (c :- e) = c :- (f $ c :- e)

l (c :- e) = (c :-) <$> e

ex (c :- e) = e

op' (c :- Binder a x b) =
  a : c :- b `op` F (length c)

cl' x (a : c :- b) =
  c :- Binder a x (b `cl` F (length c))

inBinder f t@(c :- Binder a x b) =
  ex $ cl' x $ f <<= op' t

inBinderF f t@(c :- Binder a x b) =
  fmap (ex . cl' x) $ l $ f <<= op' t

opApp e@(c :- a :@ b) = Just (c :- a, c :- b)
opApp _ = Nothing

opLam e@(c :- n :. a :\ b) = Just (c :- a, op' e)
opLam _ = Nothing

opPi e@(c :- n :. a :> b) = Just (c :- a, op' e)
opPi _ = Nothing

pattern a :@! b <- (opApp -> Just (a, b))

pattern a :\! b <- (opLam -> Just (a, b))

pattern a :>! b <- (opLam -> Just (a, b))



class FromNamed a where
  goFromNamed :: [N] -> [N] -> a -> a

fromNamed :: FromNamed a => a -> a
fromNamed = goFromNamed [] []

instance FromNamed a => FromNamed (C a) where
  goFromNamed [] [] (c :- e) = c' :- e' where
    c' = map (\(n :. a : ctx) -> n :. goFromNamed (map nam ctx) [] a) $ init $ tails c
    e' = goFromNamed (map nam c') [] e

instance FromNamed E where
  goFromNamed cf cb = \case
    M ('?':n) -> M ('?':n)
    M n -> case (elemIndex n (reverse cf), elemIndex n cb) of
      (Just i, Nothing) -> F i
      (Nothing, Just i) -> B i
    a :@ b -> goFromNamed cf cb a :@ goFromNamed cf cb b
    Binder (n :. a) x b ->
      (n :. (goFromNamed cf cb a)) `x` (goFromNamed cf (n:cb) b)
    e -> e

class ToNamed a where
  goToNamed :: [N] -> [N] -> a -> a

toNamed :: ToNamed a => a -> a
toNamed = goToNamed [] []

instance ToNamed a => ToNamed (C a) where
  goToNamed [] [] (c :- e) = c' :- e' where
    c' = map (\(n :. a : ctx) -> n :. goToNamed (map nam ctx) [] a) $ init $ tails c
    e' = goToNamed (map nam c') [] e

instance ToNamed E where
  goToNamed cf cb = \case
    M ('?':n) -> M ('?':n)
    F i -> M $ (reverse cf) !! i
    B i -> M $ cb !! i
    a :@ b -> goToNamed cf cb a :@ goToNamed cf cb b
    Binder (n :. a) x b ->
      (n :. (goToNamed cf cb a)) `x` (goToNamed cf (n:cb) b)
    e -> e
