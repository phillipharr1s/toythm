{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module TT where

import Data.List
import Data.Either
import Data.Function
import Control.Monad
import Control.Arrow

import Debug.Trace

import E
import C
import NF

pts (K i) (K j) = K j
pts a b = error $ show (a,b)

lam2pi (a :\ b) = a :> b

data TypeError = Mismatch E E E E [B] deriving(Show)

tc' (tc -> Right e) = e

-- (\ans -> trace ("{tc" ++ show j ++ " : " ++ show ans ++ "}") ans ) $

tc :: C E -> Either TypeError E
tc ce@(c :- e) = case e of
  (n :. a) :> b -> do 
    tc (c :- a)
    pts <$> tc (c :- a) <*> tc (op' ce)
  (n :. a) :\ b -> do
    tc (c :- a)
    lam2pi <$> inBinderF tc ce
  a :@ b -> do
    ta <- tc (c :- a)
    tb <- tc (c :- b)
    case (ta, tb) of
      (n :. t :> _, t') | nf' t == nf' t'
        -> pure $ nf (c :- ta :@ b)
      _ -> Left $ Mismatch ta tb a b c
  F n -> pure $ lk c n
  K i -> pure $ K (i+1)
  other -> error $ "??" ++ show ce ++ "???" ++ show other

ring =
  reverse
  [ "A" :. K 0
  , "=" :. ("x" :. M "A" :> "y" :. M "A" :> K 0)
  , "refl" :. ("x" :. M "A" :> M "=" :@ M "x" :@ M "x")
  , "=elim" :. (
      "P" :. ("x" :. M "A" :> K 0) :>
      "x" :. M "A" :>
      "y" :. M "A" :>
      "x=y" :. (M "=" :@ M "x" :@ M "y") :>
      "Px" :. (M "P" :@ M "x") :>
      M "P" :@ M "y"
    )
  , "0" :. M "A"
  , "1" :. M "A"
  , "+" :. ("x" :. M "A" :> "y" :. M "A" :> M "A")
  , "*" :. ("x" :. M "A" :> "y" :. M "A" :> M "A")
  , "+comm" :. (
    "x" :. M "A" :> 
    "y" :. M "A" :> 
    M "=" :@ (M "+" :@ M "x" :@ M "y") :@ (M "+" :@ M "y" :@ M "x")
    )
  , "*comm" :. (
    "x" :. M "A" :> 
    "y" :. M "A" :> 
    M "=" :@ (M "*" :@ M "x" :@ M "y") :@ (M "*" :@ M "y" :@ M "x")
    )
  , "+assoc" :. (
    "x" :. M "A" :>
    "y" :. M "A" :>
    "z" :. M "A" :>
    M "=" 
      :@ (M "+" :@ M "x" :@ (M "+" :@ M "y" :@ M "z")) 
      :@ (M "+" :@ (M "+" :@ M "x" :@ M "y") :@ M "z")
    )
  , "*assoc" :. (
    "x" :. M "A" :>
    "y" :. M "A" :>
    "z" :. M "A" :>
    M "=" 
      :@ (M "*" :@ M "x" :@ (M "*" :@ M "y" :@ M "z")) 
      :@ (M "*" :@ (M "*" :@ M "x" :@ M "y") :@ M "z")
    )
  , "1unit" :. (
    "x" :. M "A" :>
    M "=" :@ (M "*" :@ M "1" :@ M "x") :@ M "x"
    )
  , "0unit" :. (
    "x" :. M "A" :>
    M "=" :@ (M "+" :@ M "0" :@ M "x") :@ M "x"
    )
  ] :- M "=elim" :@ ("a" :. M "A" :\ M "=" :@ M "a" :@ M "a")

