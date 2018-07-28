-- {-# LANGUAGE 
--   DeriveFunctor
-- , PatternSynonyms 
-- , LambdaCase
-- , BangPatterns
-- , FlexibleContexts
-- #-}

module Main where

type N = String 

data T  
 = F N 
 | B Int 
 | A T T 
 | L T T 
 | P T T 
 | K Int 

 data C = C [(N,T)] T

 
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
