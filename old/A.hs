{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}

module A where

import Data.Functor.Foldable
import Data.Functor.Classes
import Text.Show.Deriving

data A f a 
 = A a (f (A f a))

instance (Show1 f, Show a) => Show (A f a) where
  showsPrec d (A a b) = 
    showParen (d >= 11)
    $ showString "A "
    . showsPrec 11 a
    . showString " "
    . showsPrec1 11 b

class Functor f => AC f a where
  combine :: f a -> a

p1 (A a _) = a

p2 (A _ b) = b

mk :: AC f a => f (A f a) -> A f a
mk dat = A (combine $ (p1 <$> dat)) dat

-- data BinTree a
--  = Branch a a
--  | Leaf
--  deriving(Show, Functor)

-- $(return [])

-- instance Show1 BinTree where
--   liftShowsPrec = $(makeLiftShowsPrec ''BinTree)

-- instance AC BinTree Int where 
--   combine (Branch a b) = a + b
--   combine Leaf = 1
