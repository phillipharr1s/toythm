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

main = print 1


data C a = [B] :- a deriving(Eq, Ord, Functor, Foldable, Traversable, Show)

infixl 2 :-

f ==< (c :- e) = c :- (f $ c :- e)

l (c :- e) = (c :-) <$> e

ex (c :- e) = e

lk (n' :. a : xs) n
 | n == n'   = a
 | otherwise = lk xs n

fr c n = if i == 0 then n else n ++ "'" ++ show i where 
  i = length $ filter ((n==) . nam) c

strip = takeWhile ('.' /=)

op' (c :- Binder (n :. a) x b) = 
  (n' :. a) : c :- (op (F n') b) 
    where n' = fr c n

cl' x (n' :. a : c :- b) =
  c :- Binder (n :. a) x (cl (F n) b)
    where n = strip n'

opApp e@(c :- a :@: b) = Just (c :- a, c :- b)
opApp _ = Nothing

opLam e@(c :- n :. a :\ b) = Just (c :- a, op' e)
opLam _ = Nothing

opPi e@(c :- n :. a :> b) = Just (c :- a, op' e)
opPi _ = Nothing

pattern a :@! b <- (opApp -> Just (a, b))

pattern a :\! b <- (opLam -> Just (a, b))

pattern a :>! b <- (opLam -> Just (a, b))

toNamed e = go [] e where
  go c (Binder (n :. a) x b) = (n' :. a') `x` b' where
    n' = fr c n
    a' = go c a
    b' = go (n' :. a : c) (op (F n') b)
  go c e = r' (go c) e

fromNamed (Binder (n :. a) x b) = 
  (n' :. fromNamed a) `x` cl (F n) (fromNamed b)
    where n' = strip n
fromNamed e = r' fromNamed e

isK (K _) = True
isK _ = False

pts (K i) (K j) = K j

tc' = go where
  go = \case
    c :- K i -> pure $ K (i+1)
    c :- F n -> pure $ lk c n
    a :@! b -> do
      ta@(tb' :>: _) <- go a
      tb <- go b
      guard (tb === tb')
      pure $ nf $ ta :@ ex b
    a :\! b -> do
      ta <- go a
      guard (isK ta)
      tb <- l $ go ==< b
      pure $ ex $ cl' (:>) tb
    a :>! b -> do 
      ta <- go a
      tb <- go b
      guard (isK ta)
      guard (isK tb)
      pure $ pts ta tb

tc (tc' -> Just a) = a



class MSub a where
  msub :: N -> E -> a -> a

instance MSub B where
  msub n t (n' :. a) = n' :. msub n t a

instance MSub E where
  msub n t e = case e of 
    M n' | n' == n -> t
    a :@ b -> msub n t a :@ msub n t b
    Binder a x b -> msub n t a `x` msub n t b
    _ -> e

instance MSub a => MSub [a] where
  msub n t a = map (msub n t) a

instance MSub a => MSub (C a) where
  msub n t (c :- e) = msub n t c :- msub n t e

data Eqn = E := E | Bot deriving(Eq, Ord, Show)

infixl 2 :=

orient (a := b) = a' := b'
  where [a', b'] = sort [a, b]

split eq = case orient eq of 
  F a :@@ as := F b :@@ bs 
   | a == b && length as == length bs 
      -> split =<< zipWith (:=) as bs
  B a :@@ as := B b :@@ bs
   | a == b && length as == length bs 
      -> split =<< zipWith (:=) as bs
  a :\: b := a' :\: b' -> split =<< [a := a', b := b']
  a :>: b := a' :>: b' -> split =<< [a := a', b := b']
  K i := K j | i == j -> []
  eq@(M _ :@@ _ := _) -> [eq]
  eq -> [Bot] -- trace "BAD:" $ traceShow eq $ [Bot]

processEqs = (split =<<) . map orient

instance MSub Eqn where
  msub n t (a := b) = msub n t a := msub n t b

data Problem = Problem I E [C B] [Eqn] deriving(Eq, Ord, Show)

instance MSub Problem where
  msub n t (Problem i a b c) = Problem i (msub n t a) (msub n t b) (msub n t c)

testP = Problem 0 T [] [B 0 := B 0]

data Delta = Delta I [(N, E)] [C B] [Eqn] deriving(Eq, Ord, Show)

applyDelta (Delta j subs goals' eqns') (Problem i term goals eqns)  = 
  foldr 
    (uncurry msub) 
    (Problem (i+j) term (f $ goals' ++ goals) (eqns ++ eqns')) subs
    where substituted = map fst subs
          f = filter (\(_ :- n :. _) -> not $ elem n substituted)

popLam (m' : fresh) (c :- m :. (n :. a :> b)) =
  Just $ Delta 1
  [(m, n :. a :\ M m')] 
  [n :. a : c :- m' :. b]
  []
popLam _ _ = Nothing

freshMetaVars (Problem i _ goals _) = [ "M" ++ show j | j <- [i..] ]

tryPopLam p@(Problem i term goals eqns) = 
  fromMaybe p $ msum $ map (go p) goals
    where 
      go p goal = 
        (\d -> applyDelta d p) <$> popLam (freshMetaVars p) goal

refute p@(Problem i term goals eqs)
  | any (== Bot) eqs' = []
  | otherwise = [Problem i term goals eqs']
  where eqs' = processEqs eqs

settle = stabilize . iterate tryPopLam

stabilize (x : y : ys) 
 | x == y = x
 | otherwise = stabilize (y : ys)

step theory = (tryR0split theory . settle =<<)

basic theory e@(n :. _) = Problem 0 (M n) [theory :- e] []

stepN theory n p = iterate (step theory) p !! n

numGoals (Problem _ _ goals _) = length goals

tryR0split c p@(Problem i e goals eqns) = do
  goal@(c' :- _) <- goals
  sym <- (F . nam <$> c) ++ (B <$> [0..length c'-1])
  pure $ applyDelta (r0split c (freshMetaVars p) goal sym) p

r0split c freshMetaVars (c' :- n :. t) sym =
  Delta
    (length newVars)
    [(n, sym :@@ (M <$> newVars))]
    newGoals -- [c' :- var :. tv | (_ :. tv : c'', var) <- zip (tail $ inits qs) newVars]
    [ret := t]
  where
    tw@(qs :>> q) = case sym of 
      F w -> lk c w
      B i -> typ (c' !! i)
    ret = nf $ tw :@@ (M <$> newVars)
    newVars = take (length qs) freshMetaVars
    newGoals = [c' :- var :. foldr op tv deps | (_ :. tv, var) <- zip qs newVars, deps <- inits (M <$> newVars) ]

finished (Problem _ _ [] _) = True
finished _ = False

showP (Problem _ e _ _) = pretty $ toNamed e

p :: [Int]
p = do 
  1 <- [2]
  return 3

q :: Maybe Int
q = do
  1 <- Just 2
  return 3

pp :: Show a => [a] -> IO ()
pp = mapM_ print

pretty p = go [] p where
  go c (B i) = c !! i
  go c (F x) = x
  go c (M v) = "?" ++ v
  go c (a :@ b) = "(" ++ go c a ++ " " ++ go c b ++ ")"
  go c (n :. a :\ b) = "\\" ++ n ++ ":" ++ go c a ++ "." ++ go (n:c) b
  go c (n :. a :> b) = "(" ++ n ++ ":" ++ go c a ++ ") -> " ++ go (n:c) b




