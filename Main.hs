{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}


module Main where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Arrow

import Debug.Trace

import E
import C

main = print 1

isK (K _) = True
isK _ = False

pts (K i) (K j) = K j

tc' = go where
  go = \case
    c :- K i -> pure $ K (i+1)
    c :- B n -> pure $ c `lk` n
    c :- a :@ b -> do
      ta@(tb' :>: _) <- go (c :- a)
      tb <- go (c :- b)
      guard (tb == tb')
      pure $ nf $ ta :@ b
    a :\! b -> do
      ta <- go a
      guard (isK ta)
      tb <- l $ go ==< b
      pure $ ex $ close (:>) tb
    a :>! b -> do 
      ta <- go a
      tb <- go b
      guard (isK ta)
      guard (isK tb)
      pure $ pts ta tb

tc (tc' -> Just a) = a

pp :: Show a => [a] -> IO ()
pp = mapM_ print

pretty p = go [] p where
  go c (K 0) = "*"
  go c (K 1) = "#"
  go c (B i) = c `ix` i
  go c (M v) = "?" ++ v
  go c (a :@ b) = "(" ++ go c a ++ " " ++ go c b ++ ")"
  go c (n :. a :\ b) = "\\" ++ n ++ ":" ++ go c a ++ "." ++ go (n:c) b
  go c (n :. a :> b) = "(" ++ n ++ ":" ++ go c a ++ ") -> " ++ go (n:c) b




