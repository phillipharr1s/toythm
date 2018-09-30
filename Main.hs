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

fr c n = n ++ "." ++ show (length c)

strip n = if null n' then n else n' where
  n' = reverse $ tail $ dropWhile ('.' /=) $ reverse n

o' (c :- e) = case q e of 
  Left (n, a, x, b) -> (n' :. a) : c :- o (V n') b
    where n' = fr c n

cl s t = go 0 t where
  go n s'
   | (s == s') = B n
   | otherwise = rb go n s'

cl' x (n :. a : c :- e) = c :- (n' :. a) `x` cl (V n) e
  where n' = strip n

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

data Ctx a = [B] :- a deriving(Eq, Ord, Show)

ex (_ :- a) = a

f ==< (c :- e) = c :- (f $ c :- e)
l (c :- e) = (c :-) <$> e

infixl 2 :-

pts (K x) (K y) = K y

isK (K _) = True
isK _ = False

tc' = go where 
  go (c :- e) = case e of 
    K n -> pure $ K (n+1)
    V n -> pure $ c `lk` n
    a :@ b -> do
      (_ :> ta) <- go (c :- a)
      tb <- go (c :- b)
      pure $ nf $ o b ta
    (n :. a) :\ b -> do
      ta <- go (c :- a)
      guard (isK ta)
      tb <- l $ go ==< o' (c :- e)
      pure $ ex $ cl' (:>) tb
    (_ :. a) :> b -> do 
      ta <- go (c :- a)
      tb <- go $ o' (c :- e)
      guard (isK ta)
      guard (isK tb)
      pure tb

tc x = tx where Just tx = tc' x

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

unit0 = ("unit0" :.) $ tdB $
  "x" :. V "Z" :>
  V "=" 
  :@ (V "+" :@ V "0" :@ V "x")
  :@ (V "x")

unit1 = ("unit1" :.) $ tdB $ 
  "x" :. V "Z" :>
  V "="
  :@ (V "*" :@ V "1" :@ V "x")
  :@ (V "x")
  

dist = ("dist" :.) $
  "x" :. V "Z" :>
  "y" :. V "Z" :>
  "z" :. V "Z" :>
  V "="
  :@ (V "*" :@ V "x" :@ (V "+" :@ V "y" :@ V "z"))
  :@ (V "+" :@ (V "*" :@ V "x" :@ V "z") :@ (V "*" :@ V "x" :@ V "z"))

ring = reverse $ 
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
  , dist
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

instance MSub a => MSub (Ctx a) where
  msub n t (c :- e) = msub n t c :- msub n t e

data Eqn = Eqn E E deriving(Eq, Ord, Show)

instance MSub Eqn where
  msub n t (Eqn a b) = Eqn (msub n t a) (msub n t b)

data Problem = Problem E [Ctx B] [Eqn] deriving(Eq, Ord, Show)

instance MSub Problem where
  msub n t (Problem a b c) = Problem (msub n t a) (msub n t b) (msub n t c)

headNF e = go (nf e) [] where
  go e args = case e of
    a :@ b -> go a (b : args)
    _ -> (e, args)

splitEqn (Eqn a b) = 
  let (ha, as) = headNF a
      (hb, bs) = headNF b
  in case (ha, hb) of
    (V _, V _) -> concatMap splitEqn $ zipWith Eqn as bs
    (_ :> a', _ :> b') -> splitEqn $ Eqn a' b'
    (_ :\ a', _ :\ b') -> splitEqn $ Eqn a' b' 

bad eq = case eq of
  Eqn (V a) (V b) | a /= b -> True
  Eqn (K a) (K b) | a /= b -> True

resolveK (c :- n :. K m) | m > 0 = ([(n, K (m-1))], [])

openLam (c :- n :. (b :> e)) = ([(n, b :\ M n')], [ b : c :- n' :. e ])
  where n' = fr c n
openLam (c :- e) = ([], [c :- e])

args q = case q of
  y :. qa :> q' -> (y :. qa) : args q'
  _ -> []

app f ((c :- y :. _) : ys) = app (f :@ V y) ys
app f [] = f

r0split (c :- n :. p) (w :. q) = ([(n, app (V w) ys)], ys) where
  ys = map (c :-) $ freshenArgs $ args q 
  freshenArgs (y :. q : yqs) = y' :. q : freshenArgs yqs
    where y' = fr c y ++ ":" ++ show (length yqs)
  freshenArgs [] = []

stdFT = applyFT openLam . applyFT resolveK

applyFT ft (Problem e exs eqns) = foldr (uncurry msub) (Problem e (concat exs') eqns) subs
  where (subs, exs') = mapM ft exs

basic e = Problem (K 0) [[] :- e] []

mID = "Ma" :. ("A" :. K 0 :> "a" :. V "A" :> V "A")

stabilize (x : y : ys) | x == y = x
stabilize (x : xs) = stabilize xs

stripCtx (Problem _ exs _) = map (\(c :- e) -> e) exs

-- thm = 
--   "x" :. V "Z" :\



