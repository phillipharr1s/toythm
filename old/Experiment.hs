{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}


module Main where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Arrow

import Debug.Trace

main = print 1

type N = String

type I = Int
 
data B
 = N :. E

data E
 = [B] :- EF

data EF
 = E :@ E
 | E :\ E
 | E :> E
