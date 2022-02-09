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


module Ring where

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

zee = "Z" :. K 0

predicate = "" :. M "Z" :> K 0

eq = "=" :. ("" :. M "Z" :> "" :. M "Z" :> K 0)

refl = "refl" :. (fromNamed $
  "x" :. M "Z" :>
  M "=" :@ M "x" :@ M "x"
  )

eqElim = "eqElim" :. (fromNamed $
  "P" :. predicate :>
  "x" :. M "Z" :>
  "y" :. M "Z" :>
  "x=y" :. (M "=" :@ M "x" :@ M "y") :>
  "Px" :. (M "P" :@ M "x") :>
  M "P" :@ M "y"
  )

zero = "0" :. M "Z"

one = "1" :. M "Z"

opA = fromNamed $ "" :. M "Z" :> "" :. M "Z" :> M "Z"

add = "+" :. opA

mul = "*" :. opA

comm = fromNamed $
  "op" :. opA :\
  "x" :. M "Z" :>
  "y" :. M "Z" :>
  M "="
  :@ (M "op" :@ M "x" :@ M "y")
  :@ (M "op" :@ M "y" :@ M "x")

assoc = fromNamed $
  "op" :. opA :\
  "x" :. M "Z" :>
  "y" :. M "Z" :>
  "z" :. M "Z" :>
  M "="
  :@ (M "op" :@ (M "op" :@ M "x" :@ M "y") :@ M "z")
  :@ (M "op" :@ M "x" :@ (M "op" :@ M "y" :@ M "z"))

addComm = "+com" :. (nf' $ comm :@ M "+")

mulComm = "*com" :. (nf' $ comm :@ M "*")

addAssoc = "+assoc" :. (nf' $ assoc :@ M "+")

mulAssoc = "*assoc" :. (nf' $ assoc :@ M "*")

unit0 = ("unit0" :.) $ fromNamed $
  "x" :. M "Z" :>
  M "="
  :@ (M "+" :@ M "0" :@ M "x")
  :@ (M "x")

unit1 = ("unit1" :.) $ fromNamed $
  "x" :. M "Z" :>
  M "="
  :@ (M "*" :@ M "1" :@ M "x")
  :@ (M "x")


dist = ("dist" :.) $
  "x" :. M "Z" :>
  "y" :. M "Z" :>
  "z" :. M "Z" :>
  M "="
  :@ (M "*" :@ M "x" :@ (M "+" :@ M "y" :@ M "z"))
  :@ (M "+" :@ (M "*" :@ M "x" :@ M "z") :@ (M "*" :@ M "x" :@ M "z"))

ring = reverse $
  [ zee
  , eq
  , refl
  , eqElim
  , zero
  , one
  , add
  , mul
  , addComm
  , mulComm
  , addAssoc
  , mulAssoc
  , unit0
  , unit1
  , dist
  ]

eqTrans = fromNamed $
  "x" :. M "Z" :\
  "y" :. M "Z" :\
  "z" :. M "Z" :\
  "x=y" :. (M "=" :@ M "x" :@ M "y") :\
  "y=z" :. (M "=" :@ M "y" :@ M "z") :\
  M "eqElim"
  :@ ("q" :. M "Z" :\ (M "=" :@ M "x" :@ M "q"))
  :@ M "y"
  :@ M "z"
  :@ M "y=z"
  :@ M "x=y"
