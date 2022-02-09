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
import PP

pts (K i) (K j) = K j
pts a b = error $ show (a,b)

lam2pi (a :\ b) = a :> b

data TypeError = Mismatch E E E E deriving(Show)

-- instance ToNamed TypeError where
--   goToNamed _ _ (Mismatch ta tb a b c) =
--     let ns = map nam c in
--     Mismatch
--       (goToNamed ns [] ta)
--       (goToNamed ns [] tb)
--       (goToNamed ns [] a)
--       (goToNamed ns [] b)
--       (case goToNamed [] [] (c :- K 0) of c' :- _ -> c')

instance ToNamed TypeError where
  goToNamed cf cb (Mismatch ta tb a b) =
    Mismatch
      (goToNamed cf cb ta)
      (goToNamed cf cb tb)
      (goToNamed cf cb a)
      (goToNamed cf cb b)

instance PrettyPrint TypeError where
  prettyPrint (Mismatch ta tb a b) =
    "Bad Application (a b):\n" ++
    "a = " ++ prettyPrint a ++
    "b = " ++ prettyPrint b ++
    "ta = " ++ prettyPrint ta ++
    "tb = " ++ prettyPrint tb

tc' (tc -> Right e) = e


printErr (Left err) = putStrLn $ prettyPrint $ toNamed err

tc :: C E -> Either (C TypeError) E
tc ce@(c :- e) = case e of
  (n :. a) :> b -> do
    tc (c :- a)
    pts <$> tc (c :- a) <*> tc (open ce)
  (n :. a) :\ b -> do
    tc (c :- a)
    lam2pi <$> inBinderF tc ce
  a :@ b -> do
    ta <- tc (c :- a)
    tb <- tc (c :- b)
    case (ta, tb) of
      (n :. t :> _, t') | nf (c :- t) == nf (c :- t')
        -> pure $ nf (c :- ta :@ b)
      _ -> Left $ c :- (Mismatch ta tb a b)
  F n -> pure $ lk c n
  K i -> pure $ K (i+1)
  other -> error $ "??" ++ show ce ++ "???" ++ show other

ringCtx =
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
  , "-" :. ("x" :. M "A" :> M "A")
  , "1/" :. ("x" :. M "A" :> M "A")
  , "-inv" :. (
    "x" :. M "A" :>
      M "="
       :@ (M "+" :@ M "x" :@ (M "-" :@ M "x"))
       :@ M "0"
    )
  , "1/inv" :. (
     "x" :. M "A" :>
       M "="
       :@ (M "*" :@ M "x" :@ (M "1/" :@ M "x"))
       :@ M "1"
    )
  ]

ring = fromNamed $ ringCtx :-
  M "=elim" :@ ("a" :. M "A" :\ M   "=" :@ M "a" :@ M "a")

eqTrans = fromNamed $ ringCtx :-
  "a" :. M "A" :\
  "b" :. M "A" :\
  "c" :. M "A" :\
  "a=b" :. (M "=" :@ M "a" :@ M "b") :\
  "b=c" :. (M "=" :@ M "b" :@ M "c") :\
  M "=elim"
  :@ ("x" :. M "A" :\ M "=" :@ M "a" :@ M "x")
  :@ M "b"
  :@ M "c"
  :@ M "b=c"
  :@ M "a=b"

plusCancel = fromNamed $ ringCtx :-
  "a" :. M "A" :\
  "b" :. M "A" :\
  "c" :. M "A" :\
  "a+c=b+c" :.
    (M "="
     :@ (M "+" :@ M "a" :@ M "b")
     :@ (M "+" :@ M "a" :@ M "c")
    ) :\
  undefined
