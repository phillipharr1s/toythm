module Main where

import Data.List
import Data.Maybe
import Control.Monad

import Debug.Trace

main = print 1

type N = String
tick = ('.':)

type I = Int

data B = N :. E
  deriving (Eq, Ord, Show)

data E
 = B I
 | V N
 | E :@ E
 | B :\ E
 | B :> E
 | K I
 | M N
 deriving (Eq, Ord, Show)

infixl 6 :.
infixl 4 :@
infixr 3 :\
infixr 3 :>
 
q e = case e of
  n :. a :\ b -> Left (n, a, (:\), b)
  n :. a :> b -> Left (n, a, (:>), b)
  _ -> Right e

r f g e = case q e of
  Left (n, a, x, b) -> (n :. f a) `x` g b
  Right (a :@ b) -> f a :@ f b
  _ -> e

r' f = r f f

rb f n = r (f n) (f $ n + 1)

o s t = go 0 t where 
  go n s'
   | (s' == B n) = s
   | otherwise = rb go n s'

o' e = case q e of 
  Left (n, a, x, b) -> o (V n) b

c s t = go 0 t where
  go n s'
   | (s == s') = B n
   | otherwise = rb go n s'

lk (n' :. a : xs) n
 | n == n'   = a
 | otherwise = lk xs n

typ (_ :. t) = t

lki ctx n = typ (ctx !! n)

tdB e = go [] e where
  go ctx e = case q e of
    Left (n, a, x, b) -> (n :. go ctx a) `x` go (n:ctx) b
    _ -> case e of
      V n -> maybe (V n) B (elemIndex n ctx)
      _ -> r' (go ctx) e 
    

fdB e = go [] e where
  go ctx e = case q e of  
    Left (n, a, x, b) ->
      let n' = freshen n ctx in 
      (n' :. go ctx a) `x` go (n':ctx) b
    _ -> case e of 
      B n -> V (ctx !! n)
      _ -> r' (go ctx) e
  freshen n ctx
   | elem n ctx = freshen (tick n) ctx
   | otherwise  = n

nf e = case e of
  ((_ :\ b) :@ a) -> nf $ o (nf a) (nf b)
  _ -> r' nf e

data Ctx a = [B] :- a

infixl 2 :-

pts (K x) (K y) = K y

tc (c :- e) = case e of 
  (a :. t) :> b -> pts (tc (c :- t)) (tc (a :. t : c :- b))
  (a :. t) :\ b -> (a :. t) :> tc ((a :. t) : c :- b)
  a :@ b -> let _ :> at = tc (c :- a) 
            in nf $ trace ("SUBST " ++ show b ++ " IN " ++ show at ++ "]") $ o b at
  B n -> c `lki` n
  V n -> c `lk`  n 
  K n -> K (n+1)

-- xx = tdB $ "a" :. K 0 :\ V "a" :@ V "a"
-- i = tdB $ "a" :. K 0 :\ V "a"

zee = "Z" :. K 0

predicate = "" :. V "Z" :> K 0

eq = "=" :. ("" :. V "Z" :> "" :. V "Z" :> K 0)

eqElim = "eqElim" :. (tdB $ 
  "P" :. predicate :> 
  "x" :. V "Z" :>
  "y" :. V "Z" :> 
  "x=y" :. (V "=" :@ V "x" :@ V "y") :> 
  "Px" :. (V "P" :@ V "x") :> 
  V "P" :@ V "y"
  )

zero = "0" :. V "Z"

one = "1" :. V "Z"

op = tdB $ "" :. V "Z" :> "" :. V "Z" :> V "Z"

add = "+" :. op

mul = "*" :. op

comm = tdB $ 
  "op" :. op :\ 
  "x" :. V "Z" :> 
  "y" :. V "Z" :> 
  V "=" 
  :@ (V "op" :@ V "x" :@ V "y") 
  :@ (V "op" :@ V "y" :@ V "x")

assoc = tdB $ 
  "op" :. op :\ 
  "x" :. V "Z" :> 
  "y" :. V "Z" :> 
  "z" :. V "Z" :> 
  V "=" 
  :@ (V "op" :@ (V "op" :@ V "x" :@ V "y") :@ V "z") 
  :@ (V "op" :@ V "x" :@ (V "op" :@ V "y" :@ V "z"))

addComm = "+com" :. (comm :@ V "+")

mulComm = "*com" :. (comm :@ V "*")

addAssoc = "+assoc" :. (assoc :@ V "+")

mulAssoc = "*assoc" :. (assoc :@ V "*")

unit0 = "unit0" :.
  ( tdB $
  "x" :. V "Z" :>
  V "=" 
  :@ (V "+" :@ V "0" :@ V "x")
  :@ (V "x")
  )

unit1 = "unit1" :.
  ( tdB $
  "x" :. V "Z" :>
  V "="
  :@ (V "*" :@ V "1" :@ V "x")
  :@ (V "x")
  )

dist = 
  "x" :. V "Z" :>
  "y" :. V "Z" :>
  "z" :. V "Z" :>
  V "="
  :@ (V "*" :@ V "x" :@ (V "+" :@ V "y" :@ V "z"))
  :@ (V "+" :@ (V "*" :@ V "x" :@ V "z") :@ (V "*" :@ V "x" :@ V "z"))

ring = 
  [ zee
  , eq
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
  ]

eqTrans = tdB $ 
  "x" :. V "Z" :\
  "y" :. V "Z" :\
  "z" :. V "Z" :\
  "x=y" :. (V "=" :@ V "x" :@ V "y") :\
  "y=z" :. (V "=" :@ V "y" :@ V "z") :\
  V "eqElim" 
  :@ ("q" :. V "Z" :\ (V "=" :@ V "x" :@ V "q"))
  :@ V "y"
  :@ V "z"
  :@ V "y=z" 
  :@ V "x=y"

-- thm = 
--   "x" :. V "Z" :\



