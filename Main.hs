{-# LANGUAGE 
  DeriveFunctor
, PatternSynonyms 
, LambdaCase
#-}
module Main where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Functor.Foldable

main = print 3

data Id 
 = Fresh Int
 | Named String
 deriving(Eq, Ord, Show) 

-- data Scope a = Scope a
--   deriving(Functor, Show)

-- data TermF a 
--  = FreeF Id 
--  | BoundF Int 
--  | AppF a a 
--  | LamF a (Scope a)
--  | PiF  a (Scope a)
--  | PropF
--  | TypeF
--  deriving(Functor, Show)

-- type Term = Fix TermF

data TermF a 
 = App a a 
 | Lam a a 

data Expr f a
 = Scope a
 | Branch (f a)
 | Bound Int

instance Functor f => Functor (Expr f) where 
  fmap f = 
    \case
    Scope  a -> Scope  (f a)
    Branch a -> Branch (f <$> a)
    Bound  k -> Bound  k

type Ctx = [Int]

type Thm = ReaderT Ctx (StateT Int Identity)

run :: Thm a -> a
run = runIdentity . (`evalStateT` 0) . (`runReaderT` [])

fresh :: Thm Id 
fresh = do 
 n <- get 
 put (n+1)
 return $ Fresh n


