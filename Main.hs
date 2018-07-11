{-# LANGUAGE 
  DeriveFunctor
, PatternSynonyms 
, LambdaCase
, BangPatterns
, FlexibleContexts
#-}
module Main where

import Control.Lens
import Control.Monad.Except 
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Functor.Foldable
import Data.Either

main = print 3

data Id 
 = Fresh !Int
 | Named !String
 deriving(Eq, Ord, Show) 

data Term 
 = Free !Id 
 | Bound !Int 
 | App !Term !Term 
 | Lam !Term !Term
 | Pi  !Term !Term 
 | Prop
 | Type
 deriving(Eq, Ord, Show)

recurseUnderBinding f g = \case
  App a b -> App (f a) (f b)
  Lam a b -> Lam (f a) (g b)
  Pi  a b -> Pi  (f a) (g b)
  e -> e

recurse f = recurseUnderBinding f f

recurseWithBindLevel go k = recurseUnderBinding (go k) (go $ k + 1)

open :: Term -> Term -> Term
open x = go 0  
  where 
    go k = 
      \case
      Bound n 
       | n == k    -> x
       | otherwise -> Bound n
      e -> recurseWithBindLevel go k e 

close :: Term -> Term -> Term 
close x = go 0 
  where 
    go k y = 
      if x == y 
        then Bound k
        else case y of
          Bound k -> Bound (k+1) 
          e -> recurseWithBindLevel go k e

sub :: Term -> Term -> Term -> Term 
sub old new = open new . close old

type Ctx = [(Id, Term)]

type Thm m = (ReaderT Ctx (StateT Int m))

liftThm = lift . lift

data TypeCheckingErr 
  = NotInScope Id
  | FlewTooHigh
  | QuantifiedOverValue
  | NotPiType
  deriving(Show)

run :: Monad m => Thm m a -> m a
run = (`evalStateT` 0) . (`runReaderT` [])

fromRight' (Right a) = a 

fresh :: Monad m => Thm m Id 
fresh = do 
 n <- get 
 put (n+1)
 return $ Fresh n

red (App a b) = 
  case red a of 
    Lam _ a' -> red $ open b a'
    e -> App e $ red b 
red e = recurse red e  

unwrap e f = case e of  
  Lam a b -> go a b f 
  Pi  a b -> go a b f 
  where 
    go a b f = do 
      x <- fresh 
      local ((x,a):) $ f (x, open (Free x) b)

tc :: Term -> Thm (Either TypeCheckingErr) Term
tc (Free a) = do
  ctx <- ask 
  case lookup a ctx of 
    Nothing -> throwError $ NotInScope a 
    Just ta -> return $ ta 
tc e@(Lam a b) = do 
  assertNotValueOrType a 
  unwrap e $ \(x, b') -> do
  tb <- tc b'
  return $ Pi a $ close (Free x) tb 
tc (App a b) = do 
  ta <- tc a 
  assertIsPi ta 
  tb <- tc b 
  return undefined
tc (Pi a b) = do 
  assertNotValueOrType a 
  assertNotValueOrType b
  ta <- tc a 
  tb <- tc b 
  return Type
tc Prop = return Type 
tc Type = throwError FlewTooHigh

assertNotValueOrType Type = throwError FlewTooHigh
assertNotValueOrType a = do 
  ta <- tc a
  if ta == Prop || ta == Type 
    then return () 
    else throwError QuantifiedOverValue

assertIsPi a = 
  if isPi a 
    then return ()
    else throwError NotPiType

isPi = \case 
  Pi _ _ -> True 
  _ -> False 

gen :: Int -> Thm [] Term
gen 1 = do 
  ctx <- ask
  liftThm $ Prop : map (Free . fst) ctx 
gen k = do 
  ka <- liftThm [1..k-1]
  let kb = k - ka 
  a <- gen ka
  join $ liftThm $ 
    [ genApps a kb 
    , genLams a kb 
    , genPis  a kb 
    ]
genApps a kb = do 
  b <- gen kb 
  return $ App a b
genLams a kb = genBinder Lam a kb 
genPis  a kb = genBinder Pi  a kb 
genBinder binder a kb = do 
  x <- fresh 
  local ((x,Prop):) $ do 
  b <- gen kb 
  return $ binder a $ close (Free x) b 

p :: Show a => [a] -> IO ()
p = putStrLn . unlines . map show
