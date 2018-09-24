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
 | E :& E
 | B :# E
 | K I
 | M N
 deriving (Eq, Ord, Show)

infixl 6 :.
infixl 4 :@
infixl 3 :&
infixr 3 :\
infixr 3 :>
infixr 3 :#
 
{-
q f g e = case e of
  n :. a :\ b -> f n a (:\) b
  n :. a :> b -> f n a (:>) b
  n :. a :# b -> f n a (:#) b
  _ -> g e
-}

q e = case e of
  n :. a :\ b -> Left (n, a, (:\), b)
  n :. a :> b -> Left (n, a, (:>), b)
  n :. a :# b -> Left (n, a, (:#), b)
  _ -> Right e

{-
r f g = q 
  (\n a x b -> (n :. f a) `x` g b)
  (\e -> case e of
    a :@ b -> f a :@ f b
    a :& b -> f a :& f b
    _ -> e
  )
-}

r f g e = case q e of
  Left (n, a, x, b) -> (n :. f a) `x` g b
  Right (a :@ b) -> f a :@ f b
  Right (a :& b) -> f a :& f b  
  _ -> e

r' f = r f f

{-
r f g e = case e of
  a :@ b -> f a :@ f b
  n :. a :\ b -> n :. f a :\ g b
  n :. a :> b -> n :. f a :> g b
  a :& b -> f a :& f b
  n :. a :# b -> n :. f a :# g b
  _ -> e
-}

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

lk _ [] = Nothing
lk n (n' :. a : xs)
 | n == n'   = Just a
 | otherwise = lk n xs 

{-
fdB e = go [] e where
  go ctx e = case e of
    a :@ b -> go ctx a :@ go ctx b
    n :. a :\ b -> n :. a :\ go (n:ctx) b
    n :. a :> b -> n :. a :> go (n:ctx) b
    a :& b -> go ctx a :& go ctx b
    n :. a :# b -> n :. a :# go (n:ctx) b
    V n -> maybe (V n) B (elemIndex n ctx)
    _ -> e
-}

tdB e = go [] e where
  go ctx e = case q e of
    Left (n, a, x, b) -> (n :. go ctx a) `x` go (n:ctx) b
    _ -> 
      case e of
        V n -> maybe (V n) B (elemIndex n ctx)
        _ -> r' (go ctx) e 
    

fdB e = go [] e where
  go ctx e = case q e of  
    Left (n, a, x, b) ->
      let n' = freshen n ctx in 
      (n' :. go ctx a) `x` go (n':ctx) b
    _ ->
      case e of 
        B n -> V (ctx !! n)
        _ -> r' (go ctx) e
  freshen n ctx
   | elem n ctx = freshen (tick n) ctx
   | otherwise  = n

nf e = case e of
  ((_ :\ b) :@ a) -> nf $ o (nf a) (nf b)
  _ -> r' nf e

xx = tdB $ "a" :. K 0 :\ V "a" :@ V "a"
i = tdB $ "a" :. K 0 :\ V "a"
