{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}


module PP (parseExpr, p, PrettyPrint, prettyPrint) where

import Prelude hiding (pi)

import Data.Either
import Data.List

import E
import C
import NF

import Text.Parsec
import Text.Parsec.Char

parens s = "(" ++ s ++ ")"
brackets s = "[" ++ s ++ "]"

p (M n) = n
p (K i) = "K" ++ show i
p (B i) = "'" ++ show i
p (F i) = "." ++ show i
p (n :. t :\ b) = brackets (n ++ " : " ++ p t) ++ p b
p (n :. t :> b) = parens (n ++ " : " ++ p t) ++ p b
p (a :@@ bs) = parens $ intercalate " " (pHeavy a : map pHeavy bs)

pHeavy e = if isHeavy e then parens (p e) else p e

isHeavy e = case e of
  _ :\ _ -> True
  _ :> _ -> True
  _ :@ _ -> True
  _ -> False

type Parse a = Parsec String () a

name :: Parse String
name = many1 (oneOf "<>?!@#$%^&*-=_+{}/\\" <|> letter <|> digit)

inParens :: Parse a -> Parse a
inParens = between (oneOf "(") (oneOf ")")

inBrackets :: Parse a -> Parse a
inBrackets = between (oneOf "[") (oneOf "]")

m :: Parse E
m = M <$> name

k :: Parse E
k = K . read <$> (oneOf "K" *> many1 digit)

b :: Parse E
b = B . read <$> (oneOf "'" *> many1 digit)

f :: Parse E
f = F . read <$> (oneOf "|" *> many1 digit)

typePair :: Parse B
typePair = do
  spaces
  n <- name
  spaces >> oneOf ":"
  e <- expr
  return (n :. e)

expr :: Parse E
expr = spaces *> (try (inParens heavyExpr) <|> heavyExpr) <* spaces

heavyExpr :: Parse E
heavyExpr = try app <|> lam <|> pi

var :: Parse E
var = k <|> b <|> f <|> m

app :: Parse E
app = (\(a : bs) -> a :@@ bs) <$> (spaces *> sepEndBy1 (try var <|> inParens heavyExpr) spaces)

lam :: Parse E
lam = do
  a <- inBrackets typePair
  b <- expr
  return (a :\ b)

pi :: Parse E
pi = do
  a <- inParens typePair
  b <- expr
  return (a :> b)

parseExpr s = case parse expr "" s of Right e -> e

class PrettyPrint a where
  prettyPrint :: a -> String

instance PrettyPrint B where
  prettyPrint (n :. t) = n ++ " : " ++ prettyPrint t

instance PrettyPrint E where
  prettyPrint = (++ "\n") . p

instance PrettyPrint a => PrettyPrint [a] where
  prettyPrint xs = concatMap (\x -> prettyPrint x) xs

instance PrettyPrint a => PrettyPrint (C a) where
  prettyPrint (c :- x) =
    prettyPrint c ++
    "-------------\n" ++
    prettyPrint x

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
  prettyPrint (Left x) = prettyPrint x
  prettyPrint (Right x) = prettyPrint x
