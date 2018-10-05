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

data B = N :. E
  deriving (Eq, Ord, Show)

infixl 6 :.

nam (n :. e) = n
typ (n :. e) = e

data E
 = B I
 | F N
 | E :@ E
 | B :\ E
 | B :> E
 | K I
 | M N
 deriving (Eq, Ord, Show)

infixl 4 :@
infixr 3 :\
infixr 3 :> 

pattern P = K 0
pattern T = K 1

asBinder = \case
  a :\ b -> Just $ (a, (:\), b)
  a :> b -> Just $ (a, (:>), b)
  _ -> Nothing

pattern Binder a x b <- (asBinder -> Just (a, x, b))
  where Binder a x b = x a b

splitApp = second reverse . go where
  go = \case
    a :@ b -> (h, b : cs) where (h, cs) = go a
    e -> (e, [])

instance Eq (B -> E -> E) where
  x == y = 
    x ("" :. B 0) (B 0) 
    ==
    y ("" :. B 0) (B 0)

splitBinder x = \case
  Binder a x' b | x == x' -> (h, a : cs) 
    where (h, cs) = splitBinder x b
  e -> (e, [])

splitLam = splitBinder (:\)

splitPi = splitBinder (:>)

pattern a :@@ bs <- (splitApp -> (a, bs))
  where a :@@ bs = foldl (:@) a bs

pattern (:\\) :: [B] -> E -> E
pattern as :\\ b <- (splitLam -> (b, as))
  where as :\\ b = foldr (:\) b as

pattern (:>>) :: [B] -> E -> E
pattern as :>> b <- (splitPi -> (b, as))
  where as :>> b = foldr (:>) b as

r f g = \case
  Binder (n :. a) x b -> (n :. f a) `x` g b
  a :@ b -> f a :@ f b
  e -> e

r' f = r f f

rb f n = r (f n) (f $ n + 1)

op t = go 0 where
  go i = \case
   e | e == B i -> t
     | otherwise -> rb go i e

cl t = go 0 where
  go i = \case
   e | e == t -> B i
     | otherwise -> rb go i e

nf = \case
  (nf -> a) :@ (nf -> b) 
   | _ :\ f <- a -> nf $ op b f
   | otherwise -> a :@ b
  e -> r' nf e

data C a = [B] :- a

infixl 2 :-

f ==< (c :- e) = c :- (f $ c :- e)

l (c :- e) = (c :-) <$> e

ex (c :- e) = e

lk (n' :. a : xs) n
 | n == n'   = a
 | otherwise = lk xs n

fr c n = if i == 0 then n else n ++ "." ++ show i where 
  i = length $ filter ((n==) . nam) c

strip = takeWhile ('.' /=)

op' (c :- Binder (n :. a) x b) = 
  (n' :. a) : c :- (op (F n') b) 
    where n' = fr c n

cl' x (n' :. a : c :- b) =
  c :- Binder (n :. a) x (cl (F n) b)
    where n = strip n'

toNamed (c :- Binder (n :. a) x b) = (n' :. a') `x` b' where
  n' = fr c n
  a' = toNamed (c :- a)
  b' = toNamed (n' :. a' : c :- op (F n') b)
toNamed (c :- e) = r' (toNamed . (c :-)) e

fromNamed (Binder (n :. a) x b) = 
  (n' :. fromNamed a) `x` cl (F n) (fromNamed b)
    where n' = strip n
fromNamed e = r' fromNamed e

isK (K _) = True
isK _ = False

tc' = go where
  go (c :- e) = case e of
    K i -> pure $ K (i+1)
    F n -> pure $ lk c n
    a :@ b -> do
      _ :> ta <- go (c :- a)
      tb <- go (c :- b)
      pure $ nf $ op b ta
    n :. a :\ b -> do
      ta <- go (c :- a)
      guard (isK ta)
      tb <- l $ go ==< op' (c :- e)
      pure $ ex $ cl' (:>) tb
    _ :. a :> b -> do 
      ta <- go (c :- a)
      tb <- go $ op' (c :- e)
      guard (isK ta)
      guard (isK tb)
      pure tb

tc (tc' -> Just a) = a

pts (K i) (K j) = K j

----


sq = fromNamed $
  "A" :. P :\ 
  "f" :. ("x" :. F "A" :> "y" :. F "A" :> F "A") :\
  F "f" :@ F "x" :@ F "x"
