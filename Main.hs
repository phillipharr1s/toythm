module Main where

import Data.List
import Data.Maybe
import Control.Monad

import Debug.Trace

-- delete a (a':as)
--  | a == a' = delete a as
--  | otherwise = a' : delete a as

-- as \\ (b : bs) = (delete b as) \\ bs
-- as \\ [] = as 

-- isJust (Just _) = True
-- isJust _ = False

main = print 1 

type N = String 

infixl 5 :& 
infixr 4 :\. 
infixr 4 :->
infixl 3 :|-

data T  
 = F N 
 | B Int 
 | T :& T 
 | T :\. T 
 | T :-> T 
 | K Int 
 deriving(Ord, Show)

r f g (a :& b) = f a :& f b
r f g (a :\. b) = f a :\. g b
r f g (a :-> b) = f a :-> g b 
r f g t = t 

rb f n = r (f n) (f $ n + 1)

o s t = go 0 t 
  where 
    go n s'
     | (s' == B n) = s 
     | otherwise  = rb go n s'

c s t = go 0 t 
  where 
    go n s' 
     | (s == s') = B n 
     | otherwise = rb go n s' 

nf (a :& b) = 
  case nf a of 
    _ :\. a' -> o (nf b) a' 
    a' -> a' :& (nf b)
nf (a :\. b) = nf a :\. nf b 
nf (a :-> b) = nf a :-> nf b 
nf t = t 

a === b = 
  case (a, b) of
    (F n, F n') -> n == n'
    (B n, B n') -> n == n'
    (K n, K n') -> n == n'
    (a :&  b, a' :&  b') -> a === a' && b === b'
    (a :\. b, a' :\. b') -> a === a' && b === b'
    (a :-> b, a' :-> b') -> a === a' && b === b'
    _ -> False

instance Eq T where
  a == b = (nf a === nf b)

data C a
 = [(N,T)] :|- a 
 deriving(Eq, Ord, Show)

instance Functor C where
  fmap f (ctx :|- t) = ctx :|- f t

f =<= (ctx :|- b) = ctx :|- f (ctx :|- b)
a =>= f = (f =<= a)

ex (_ :|- t) = t

lift (ctx :|- t) = (ctx :|-) <$> t

fr ctx = F $ head $ map return ['a'..] \\ map fst ctx

pop (ctx :|- t) = 
  case t of 
    a :\. b -> go a b
    a :-> b -> go a b
  where
    go a b = (f, a):ctx :|- o (F f) b
    F f = fr ctx 

push x ((n,tn):ctx :|- t) = ctx :|- tn `x` c (F n) t

use ctx = (ctx :|-) $ map (F . fst) ctx

isK (K _) = True
isK _ = False 

pts a b = b 

tc e@(ctx :|- t) = 
  case t of
    K n -> return $ K (n+1)
    F n -> lookup n ctx
    a :& b -> do
      ta <- tc (ctx :|- a)
      tb <- tc (ctx :|- b)
      case ta of 
        tb' :-> ta'
         | tb' == tb -> return $ o a ta'
        _ -> Nothing
    a :\. b -> do
      ta <- tc (ctx :|- a)
      guard (isK ta)
      tb <- lift $ tc =<= pop e
      return $ ex $ push (:->) tb
    a :-> b -> do
      ta <- tc (ctx :|- a)
      guard (isK ta)
      tb <- ex $ tc =<= pop e
      guard (isK tb)
      return $ pts ta tb

std = [("A", K 0)]

isLevel k (ctx :|- t) = ttt == Just (K k)
  where ttt = tc =<< lift (tc =<= (ctx :|- t))

split n = zip (reverse [0..n-1]) [0..n-1]

good ctx t = isJust $ tc $ ctx :|- t

enum k n ctx = 
  filter (good ctx) $ enumHead k n ctx ++ enumBind k n ctx

enumHead k 0 ctx =
  map ex $ filter (isLevel k) $ lift $ use ctx
enumHead k n ctx = do
  (na, nb) <- split n
  a <- enumHead k na ctx
  b <- enumHead k nb ctx
  let t = a :& b
  return $ t

enumBind k 0 ctx = []
enumBind k n ctx = do
  (na, nb) <- split n
  a <- (if na == 0 then (K 0:) else id) $ enum 1 na ctx
  let F f = fr ctx
  b <- enum k nb ((f, a):ctx)
  let x = if k == 0 then (:\.) else (:->)
  let t = a `x` c (F f) b
  return $ t

pp a = putStrLn $ unlines $ map show a

-- q = putStrLn $ unlines $ map show $ sort $ nub $ map (tc . ([] :|-)) $ enum 5 []

-- enumProps n ctx = filter (\a -> tc ([] :|- a) == Just (K 0)) $ enum 5 ctx

size (a :\. b) = size b
size (a :-> b) = size b
size t = asize t

asize (a :&  b) = asize a + asize b
asize (a :\. b) = asize a + asize b
asize (a :-> b) = asize a + asize b
asize _ = 1

proves ctx t tt = tc (ctx :|- t) == Just tt

proof limit ctx thm = take 1 $ 
  [ t 
  | n <- [0..limit] 
  , t <- pfs !! n 
  , proves ctx t thm
  ]

proof0 limit ctx thm = 
  case proof limit ctx thm of
    []  -> Nothing
    t:_ -> Just t

quality (Nothing, _) = -100
quality (Just t, thm) = 
  size t - size thm


pfs  = [ enum 0 n [] | n <- [0..]]
thms = [ enum 1 n [] | n <- [0..]]

-- K 0 :\. (B 0 :\. (K 0 :\. ((B 2 :-> B 1) :\. B 0 :& B 2)))
-- pp $ map (\x -> (p0 6 [] x,x)) $ thms !! 3
Just thm = tc $ [] :|- K 0 :\. (B 0 :\. (K 0 :\. ((B 2 :-> B 1) :\. B 0 :& B 2)))
-- pp $ map (\x -> (quality x, x)) $ map (\x -> (proof0 6 [] x, x)) $ thms !! 6






-- {-# LANGUAGE 
--   DeriveFunctor
-- , PatternSynonyms 
-- , LambdaCase
-- , BangPatterns
-- , FlexibleContexts
-- #-}
-- module Main where

-- import Control.Lens
-- import Control.Monad.Except 
-- import Control.Monad.Reader
-- import Control.Monad.State.Strict

-- import Data.Functor.Foldable
-- import Data.Either
-- import Data.List
-- import qualified Data.Set as S

-- import Debug.Trace

-- main = print 3

-- demo1 = p 
--  $ nub 
--  $ runIdentity 
--  $ run 
--  $ mapM (runExceptT . tc) 
--  $ run 
--  $ gen 5

-- data Id 
--  = Fresh !Int
--  | Named !String
--  deriving(Eq, Ord, Show) 

-- data Term 
--  = Free !Id 
--  | Bound !Int 
--  | App !Term !Term 
--  | Lam !Term !Term
--  | Pi  !Term !Term 
--  | Prop
--  | Type
--  deriving(Eq, Ord, Show)

-- recurseUnderBinding f g = \case
--   App a b -> App (f a) (f b)
--   Lam a b -> Lam (f a) (g b)
--   Pi  a b -> Pi  (f a) (g b)
--   e -> e

-- recurse f = recurseUnderBinding f f

-- recurseWithBindLevel go k = recurseUnderBinding (go k) (go $ k + 1)

-- open :: Term -> Term -> Term
-- open x = go 0  
--   where 
--     go k = 
--       \case
--       Bound n 
--        | n == k    -> x
--        | otherwise -> Bound n
--       e -> recurseWithBindLevel go k e 

-- close :: Term -> Term -> Term 
-- close x = go 0 
--   where 
--     go k y = 
--       if x == y 
--         then Bound k
--         else case y of
--           Bound k -> Bound k 
--           e -> recurseWithBindLevel go k e

-- sub :: Term -> Term -> Term -> Term 
-- sub old new = open new . close old

-- type Ctx = [(Id, Term)]

-- type Thm m = (ReaderT Ctx (StateT Int m))

-- liftThm = lift . lift

-- data TypeCheckingErr 
--   = NotInScope Id
--   | FlewTooHigh
--   | QuantifiedOverValue
--   | NotPiType
--   | Mismatch Term Term
--   deriving(Eq, Ord, Show)

-- run :: Monad m => Thm m a -> m a
-- run = (`evalStateT` 0) . (`runReaderT` [])

-- runWithCtx :: Monad m => Ctx -> Thm m a -> m a
-- runWithCtx ctx = (`evalStateT` 0) . (`runReaderT` ctx)

-- fromRight' (Right a) = a 

-- fresh :: MonadState Int m => m Id 
-- fresh = do 
--  n <- get 
--  put (n+1)
--  return $ Fresh n

-- red (App a b) = 
--   case red a of 
--     Lam _ a' -> red $ open b a'
--     e -> App e $ red b 
-- red e = recurse red e  

-- unwrap :: 
--   (MonadReader Ctx m,
--   MonadState Int m ) => 
--   Term -> ((Id, Term) -> m Term) -> m Term
-- unwrap e f = case e of  
--   Lam a b -> go a b f 
--   Pi  a b -> go a b f 
--   where
--     go :: (MonadState Int m, MonadReader Ctx m) => Term -> Term -> ((Id, Term) -> m Term) -> m Term
--     go a b f = do 
--       x <- fresh 
--       local ((x,a):) $ f (x, open (Free x) b)

-- tc :: Monad m => Term -> ExceptT TypeCheckingErr (Thm m) Term 
-- tc (Free a) = do
--   ctx <- ask 
--   case lookup a ctx of 
--     Nothing -> throwError $ NotInScope a 
--     Just ta -> return $ ta 
-- tc e@(Lam a b) = do 
--   assertNotValueOrType a 
--   unwrap e $ \(x, b') -> do
--   tb <- tc b'
--   return $ Pi a $ close (Free x) tb 
-- tc (App a b) = do 
--   ta <- tc a 
--   assertIsPi ta 
--   let (Pi tb' ta') = ta 
--   tb <- tc b
--   if red tb == red tb' 
--     then return $ open b ta'
--     else throwError (Mismatch tb tb')
-- tc e@(Pi a b) = do 
--   assertNotValueOrType a 
--   ta <- tc a 
--   unwrap e $ \(x, b') -> do
--   assertNotValueOrType b'
--   tb <- tc b'
--   return Type
-- tc Prop = return Type 
-- tc Type = throwError FlewTooHigh

-- assertNotValueOrType Type = throwError FlewTooHigh
-- assertNotValueOrType a = do 
--   ta <- tc a
--   if ta == Prop || ta == Type 
--     then return () 
--     else throwError QuantifiedOverValue

-- assertIsPi a = 
--   if isPi a 
--     then return ()
--     else throwError NotPiType

-- isPi = \case 
--   Pi _ _ -> True 
--   _ -> False 

-- genTo :: Int -> Thm [] Term 
-- genTo k = do 
--   k' <- liftThm [1..k]
--   gen k'

-- spy x = trace ("!" ++ show x) x

-- gen :: Int -> Thm [] Term
-- gen 1 = do 
--   ctx <- ask
--   liftThm $ Prop : map (Free . fst) ctx
-- gen k = do 
--   ka <- liftThm [1..k-1]
--   let kb = k - ka 
--   a <- gen ka
--   assertWellTyped a
--   join $ liftThm $ 
--     [ genApps a kb 
--     , genLams a kb 
--     , genPis  a kb 
--     ]
-- genApps a kb = do 
--   b <- gen kb
--   let e = App a b 
--   assertWellTyped e 
--   return e
-- genLams a kb = genBinder Lam a kb 
-- genPis  a kb = genBinder Pi  a kb 
-- genBinder binder a kb = do 
--   x <- fresh 
--   local ((x, a):) $ do 
--   b <- gen kb 
--   let e = binder a $ close (Free x) b 
--   assertWellTyped e 
--   return e 

-- assertWellTyped a = do 
--   ta <- runExceptT $ tc a 
--   guard (isRight ta)

-- isConstant a = 
--   (close (Free $ Named "__IMPOSSIBLE__") $ open Type a) == a 

-- isClosedTerm (Bound _) = False
-- isClosedTerm (App a b) = isClosedTerm a && isClosedTerm b 
-- isClosedTerm (Lam a b) = 
--   isClosedTerm a && (isClosedTerm $ open Type b) 
-- isClosedTerm (Pi  a b) = 
--   isClosedTerm a && (isClosedTerm $ open Type b) 
-- isClosedTerm _ = True

-- conclusions e = filter isClosedTerm $ unsafeConclusions e 
 
-- unsafeConclusions e@(Pi a b) = e : unsafeConclusions b 
-- unsafeConclusions e = [e]

-- redundant (Pi  a b) = isConstant b 
-- redundant (Lam a b) = isConstant b
-- redundant _ = False

-- getContextFreeType = fromRight' . runIdentity . run . runExceptT . tc 

-- getType ctx = fromRight' . runIdentity . runWithCtx ctx . runExceptT . tc

-- getConclusions = conclusions . getContextFreeType

-- sample k = 
--    map (\a -> (a, getContextFreeType a))
--  $ run 
--  $ genTo k

-- sampleOnA k = 
--   map (\a -> (a, getType aContext a)) 
--   $ runWithCtx aContext $ genTo k 

-- aContext = [(Named "X", Prop)]

-- -- pool k = nub $ map snd novelties
-- --   where 
-- --     novelties = (`filter` s) 
-- --       (\(a, ta) -> 
-- --          if redundant a then True else True
-- --       )
-- --     s = sample k 

-- pool k = nub $ map snd novelties
--   where 
--     novelties = (`filter` s) 
--       (\(a, ta) -> 
--         (5 + adjustedSize a > size ta)
--         && (not $ redundant a)
--         && (all (not . flip elem theorems) (tail $ conclusions ta))
--       )
--     s = sampleOnA k 
--     theorems = map snd s

-- size (App a b) = 1 + size a + size b 
-- size (Lam a b) = 1 + size a + size b 
-- size (Pi  a b) = 1 + size a + size b 
-- size e = 1

-- adjustedSize (Lam a b) = adjustedSize b 
-- adjustedSize a = size a 

-- pretty pool (q:qs) ctx (Lam Prop a) = 
--  "(\\" ++ q ++ ": * . " ++ pretty pool qs (q:ctx) a ++ ")"
-- pretty (p:ps) qool ctx (Lam a b) = 
--   "(\\" ++ p ++ " : " 
--   ++ pretty ps qool ctx a 
--   ++ " . " ++ pretty ps qool (p:ctx) b ++ ")"
-- pretty pool (q:qs) ctx (Pi Prop a) = 
--   "(" ++ q ++ " : * . " ++ pretty pool qs (q:ctx) a ++ ")"
-- pretty (p:ps) qool ctx (Pi a b) = 
--   if isConstant b
--   then "(" ++ pretty (p:ps) qool ctx a ++ " => " 
--        ++ pretty (p:ps) qool ("&":ctx) b ++ ")"
--   else 
--     "(" ++ p ++ " : " 
--     ++ pretty ps qool ctx a 
--     ++ " . " ++ pretty ps qool (p:ctx) b ++ ")"
-- pretty pool qool ctx (App a b) = 
--   "(" ++ pretty pool qool ctx a ++ ")(" ++ pretty pool qool ctx b ++ ")"
-- pretty _ _ ctx (Bound k) = ctx !! k
-- pretty _ _ ctx (Free (Named name)) = name
-- pretty _ _ _ Prop = "*"
-- pretty _ _ _ Type = "@"

-- pp = 
--   pretty 
--   (map pure "abcdefghijklmnopqrstuvwxyz")
--   (map pure "ABCDEFGHIJKLMNOPQRSTUVWXYZ") 
--   []

-- ppp = putStrLn . unlines . map pp

-- p :: Show a => [a] -> IO ()
-- p = putStrLn . unlines . map show
