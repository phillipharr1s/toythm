{-# LANGUAGE 
  PatternSynonyms
, TypeOperators 
#-}

module Main where

import Data.List
import Data.Maybe
import Control.Monad

import Debug.Trace

main = print 1

type N = String

data FV = FV N Int

fr c n = (n, length c)

data B = N :. E

data E
 = Free FV
 | Bound Int
 | E :@ E
 | B :\ E
 | B :> E
 | K Int
 | M N
 deriving(Eq, Show, Ord)

data a :- b = a :- b

