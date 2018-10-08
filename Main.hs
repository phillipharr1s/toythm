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
  _ :\ (f :@ B 0) | op (K 0) f == f -> f
  e -> r' nf e

class Equiv a where
  (===) :: a -> a -> Bool

instance Equiv E where
  x === y = stripNames (nf x) == stripNames (nf y)

stripNames = \case 
  Binder (n :. a) x b -> ("" :. stripNames a) `x` stripNames b
  e -> r' stripNames e

data C a = [B] :- a deriving(Eq, Ord, Show)

instance Functor C where
  fmap f (c :- e) = c :- f e

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
      (_ :. tb') :> ta <- go (c :- a)
      tb <- go (c :- b)
      guard (tb === tb')
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
      pure $ pts ta tb

tc (tc' -> Just a) = a

pts (K i) (K j) = K j

data Constraint
 = E := E
 | [B] :? B


class MSub a where
  msub :: N -> E -> a -> a


instance MSub B where
  msub n t (n' :. a) = n' :. msub n t a

instance MSub E where
  msub n t e = case e of 
    M n' | n' == n -> t
    a :@ b -> msub n t a :@ msub n t b
    a :> b -> msub n t a :> msub n t b
    a :\ b -> msub n t a :\ msub n t b
    _ -> e

instance MSub a => MSub [a] where
  msub n t a = map (msub n t) a

instance MSub a => MSub (C a) where
  msub n t (c :- e) = msub n t c :- msub n t e

data Eqn = Eqn E E deriving(Eq, Ord, Show)

instance MSub Eqn where
  msub n t (Eqn a b) = Eqn (msub n t a) (msub n t b)

data Problem = Problem E [C B] [Eqn] deriving(Eq, Ord, Show)

instance MSub Problem where
  msub n t (Problem a b c) = Problem (msub n t a) (msub n t b) (msub n t c)

data Delta = Delta [(N, E)] [C B] [Eqn] deriving(Eq, Ord, Show)

headNF e = go (nf e) [] where
  go e args = case e of
    a :@ b -> go a (b : args)
    _ -> (e, args)

applyDelta (Delta subs exs' eqns') (Problem e exs eqns)  = 
  foldr 
    (uncurry msub) 
    (Problem e (f $ exs ++ exs') (eqns ++ eqns')) subs
    where substituted = map fst subs
          f = filter (\(_ :- n :. _) -> not $ elem n substituted)

-- splitEqn (Eqn a b) = 
--   let (ha, as) = headNF a
--       (hb, bs) = headNF b
--   in case (ha, hb) of
--     (F _, F _) -> concatMap splitEqn $ zipWith Eqn as bs
--     (_ :> a', _ :> b') -> splitEqn $ Eqn a' b'
--     (_ :\ a', _ :\ b') -> splitEqn $ Eqn a' b' 

bad eq = case eq of
  Eqn (as :>> (F _ :@@ _)) (bs :>> (F _ :@@ _)) | length as /= length bs -> True
  Eqn (F a :@@ as) (F b :@@ bs) 
    | a /= b -> True
    | length as /= length bs -> True
  Eqn (K a) (K b) | a /= b -> True
  Eqn (K a) (K b) | a == b -> False
  Eqn (K _) _ -> True
  Eqn _ (K _) -> True
  _ -> False

splitEqn = \case
  Eqn a b | a == b -> []
  Eqn (F a :@@ as) (F b :@@ bs) 
    | length as == length bs , a == b 
        -> splitEqn =<< zipWith (Eqn) (F a : as) (F b : bs )
  Eqn a b -> [Eqn a b]

resolveK = \case
  c :- n :. K m | m > 0 -> Delta [(n, K (m-1))] [] []
  _ -> Delta [] [] []

popLam exs (c :- m :. (n' :. a :> t)) = 
  Delta
    [(m, n'' :. a :\ M m' )]
    [n'' :. a : c :- m' :. t']
    []
  where
    n'' :. _ : _ :- t' = op' (exs ++ c :- (n' :. a :> t))
    m' = fr (exs ++ c) m
popLam _ _ = Delta [] [] []

r0split exs (c :- n :. t) w = 
  Delta 
    [(n, F w :@@ (M . nam <$> bindings))]
    ((c :-) <$> bindings )
    [Eqn ret t]
  where 
    tw = lk c w
    go acc q@(_ :- n :. a :> tws) = 
      let q'@(n' :. a : _ :- tws') = (op (M n') . cl (F n')) <$> op' q
      in go (n' :. a : acc) q'
    go acc tw = (acc, tw)
    (bindings, _ :- ret) = go [] (exs ++ c :- tw)
-- Problem ("FALSE" :. ("A" :. K 0 :> F "A") :\ ("B" :. K 0 :\ M "EXPLOSION.1.1")) [["B" :. K 0,"FALSE" :. ("A" :. K 0 :> F "A")] :- "EXPLOSION.1.1" :. F "B"] []
tryR0split p@(Problem e exs eqns) = do
  existential@(c :- _) <- exs
  (w :. _) <- c
  tryDelta $ applyDelta (r0split (map ex exs) existential w) p

tryPopLam p@(Problem e exs eqns) = do
  existential <- exs
  tryDelta $ applyDelta (popLam (map ex exs) existential) p

tryDelta p@(Problem e exs eqns)
 | any bad eqns = []
 | otherwise = [p]

basic e@(n :. _) = Problem (M n) [theory :- e] []

mID = "Ma" :. ("A" :. K 0 :> "a" :. F "A" :> F "A")

stabilize (x : y : ys) | x == y = x
stabilize (x : xs) = stabilize xs

stripCtx (Problem _ exs _) = map (\(c :- e) -> e) exs

optional f x = x : f x

wash = 
    nub
  . (tryDelta =<<)
  . map (\(Problem a b c) -> Problem a b (stabilize $ iterate (splitEqn =<<) c))
  . (tryR0split =<<) 
  . (tryPopLam =<<)

letsgo t = (iterate wash [basic t]) !! 5
-- nub $ filter finished $ 

finished (Problem _ [] []) = True
finished (Problem _ _  _) = False

aT = "A" :. (nf $ fromNamed $ K 0)

eqT = "=" :. (nf $ fromNamed $ 
  "x" :. F "A" :> "y" :. F "A" :> K 0
  )

refl = "refl" :. (nf $ fromNamed $ 
  "x" :. F "A" :> F "=" :@ F "x" :@ F "x"
  )

elim = "elim" :. (nf $ fromNamed $
  "P" :. (
    "x" :. F "A" :> 
    "y" :. F "A" :>
    "x=y" :. (F "=" :@ F "x" :@ F "y") :> 
    K 0
  ) :> 
  "Prefl" :. (
    "x" :. F "A" :>
    F "P" :@ (F "refl" :@ F "x")
  ) :> 
  "x" :. F "A" :> 
  "y" :. F "A" :> 
  "x=y" :. (F "=" :@ F "x" :@ F "y") :>
  F "P" :@ F "x=y"
  )

theory = ["P" :. K 0, eqT, refl, elim] -- [elim, refl, eqT, aT]

false = "Q" :. K 0 :> F "Q"

notT p = p `implies` false

implies p q = "_" :. p :> q

dni = "DNI" :. (implies (F "P") (notT $ notT $ F "P"))

eqTrans = fromNamed $ 
  "x" :. F "P" :\
  "y" :. F "P" :\
  "z" :. F "P" :\
  "x=y" :. (F "=" :@ F "x" :@ F "y") :\
  "y=z" :. (F "=" :@ F "y" :@ F "z") :\
  F "eqElim" 
  :@ ("q" :. F "P" :\ (F "=" :@ F "x" :@ F "q"))
  :@ F "y"
  :@ F "z"
  :@ F "y=z" 
  :@ F "x=y"

pp :: Show x => [x] -> IO ()
pp = mapM_ print

ff = filter finished

----


sq = fromNamed $
  "A" :. P :\ 
  "f" :. ("x" :. F "A" :> "y" :. F "A" :> F "A") :\
  "x" :. F "A" :\
  F "f" :@ F "x" :@ F "x"
