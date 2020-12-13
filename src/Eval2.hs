{-# LANGUAGE RecursiveDo #-}

module Eval2 where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Bifunctor (Bifunctor (second))
import qualified Data.Map as Map
import Data.Vec.Lazy (Vec (VNil))
import Parser
import Test.HUnit
import Test.QuickCheck
  ( Args (maxSize, maxSuccess),
    Property,
    Testable,
    quickCheckWith,
    stdArgs,
    (==>),
  )
import qualified TypeInf as TI
import Types

type StepResult = Either String Expression

(🔥) :: (Variable, Expression) -> Expression -> Expression
(x, e) 🔥 (Var y)
  | x == y = e
s 🔥 (Annot e' ty) = Annot (s 🔥 e') ty
s 🔥 If e e1 e2 = If (s 🔥 e) (s 🔥 e1) (s 🔥 e2)
s@(x, _) 🔥 Case e bs = Case (s 🔥 e) (map caseMapper bs)
  where
    caseMapper :: (Pattern, Expression) -> (Pattern, Expression)
    caseMapper (p, e)
      | patBound p = (p, e)
      | otherwise = (p, s 🔥 e)

    -- check if the variable was bound in the pattern
    patBound :: Pattern -> Bool
    patBound (P _ ps) = foldr (\p acc -> patBound p || acc) False ps
    patBound (VarP y) = x == y
    patBound _ = False
s 🔥 Op b l r = Op b (s 🔥 l) (s 🔥 r)
s@(x, _) 🔥 Lam y e'
  | x == y = Lam y e'
  | otherwise = Lam y (s 🔥 e')
s@(x, _) 🔥 Mu y e'
  | x == y = Mu y e'
  | otherwise = Mu y (s 🔥 e')
s 🔥 App e es = App (s 🔥 e) (map (s 🔥) es)
s@(x, _) 🔥 exp@(Let y e1 e2) 
  | x == y = exp
  | otherwise = Let y (s 🔥 e1) (s 🔥 e2)
-- s 🔥 PC 
_ 🔥 e = e

isValue :: Expression -> Bool
isValue (IntExp _) = True
isValue (BoolExp _) = True
isValue (Lam _ _) = True
isValue (C _) = True
isValue (App (C _) es) = all isValue es
-- isValue (PC _ _) = True
isValue _ = False

applyToFirstWhich :: Monad m => (a -> Bool) -> (a -> m a) -> [a] -> m [a]
applyToFirstWhich p f (x : xs)
  | p x = do
    res <- f x
    return (res : xs)
  | otherwise = do
    rest <- applyToFirstWhich p f xs
    return (x : rest)
applyToFirstWhich p f [] = return []

step :: Expression -> Either String Expression
step (App e es)
  | not (isValue e) = do
    s <- step e
    return $ App s es
step (App (Lam x e') (e : es)) = return $ App ((x, e) 🔥 e') es
step e@(App d@(C _) es)
  | all isValue es = return e
  | otherwise = App d <$> applyToFirstWhich (not . isValue) step es
step (App (App e es) es') = return $ App e (es ++ es')
step (App e []) = return e
step (Let v e1 e2) = return $ (v, Mu v e1) 🔥 e2
step (Mu f e) = return $ (f, Mu f e) 🔥 e
step (Case e es)
  | isValue e = findCase e es
  | otherwise = do
    e' <- step e
    return $ Case e' es
step (If e e1 e2)
  | not (isValue e) = do
    e' <- step e
    return $ If e' e1 e2
step (If (BoolExp b) e1 e2)
  | b = return e1
  | not b = return e2
step (Op b l r)
  | not (isValue l) = do
    l' <- step l
    return $ Op b l' r
  | not (isValue r) = do
    r' <- step r
    return $ Op b l r'
  | otherwise = evalB b l r
step (Annot e _) = step e
step s
  | isValue s = return s
  | otherwise = throwError $ show s <> " doesn't step"

eval :: Expression -> Either String Expression
eval e = do
  s <- step e
  if isValue s then return s else eval s

evalIO :: Expression -> IO ()
evalIO e = do
  putStrLn (display e)
  putStrLn "---------------------"
  let res = step e
  case res of
    Left s -> putStrLn s
    Right e' -> do
      if isValue e' then return () else evalIO e'

topEval :: FilePath -> IO ()
topEval fs = do
  exp <- parseFile fs
  print exp
  evalIO exp

-- takes a basically eval'd function and tries to eval the operator
evalB :: Bop -> Expression -> Expression -> StepResult
evalB Plus (IntExp i1) (IntExp i2) = return (IntExp (i1 + i2))
evalB Minus (IntExp i1) (IntExp i2) = return (IntExp (i1 - i2))
evalB Times (IntExp i1) (IntExp i2) = return (IntExp (i1 * i2))
evalB Gt (IntExp i1) (IntExp i2) = return (BoolExp (i1 > i2))
evalB Ge (IntExp i1) (IntExp i2) = return (BoolExp (i1 >= i2))
evalB Lt (IntExp i1) (IntExp i2) = return (BoolExp (i1 < i2))
evalB Le (IntExp i1) (IntExp i2) = return (BoolExp (i1 <= i2))
evalB _ _ _ = throwError "Invalid argument to binary operator"

type Substitution = [(Variable, Expression)]

patternMatch :: Expression -> Pattern -> Either String Substitution
patternMatch (IntExp i) (IntP p) | i == p = return []
patternMatch (BoolExp b) (BoolP p) | b == p = return []
patternMatch e (VarP x) = return [(x, e)]
patternMatch (C dt) (P dt' []) | getDCName dt == getDCName dt' = return []
patternMatch (App (C dt) l) (P dt' ps) =
  if getDCName dt == getDCName dt' && length l == length ps
    then
      foldM
        ( \acc (v, p) -> do
            res <- patternMatch v p
            return (res ++ acc)
            --  in (fst res && fst acc, snd res)
        )
        []
        (zip l ps)
    else throwError "Bro no"
patternMatch _ _ = throwError "BROOO"

-- potential quickcheck property
-- everything that's not a value steps to something

-- -- | Searches through all cases, and tries to match against a simplified expression
findCase :: Expression -> [(Pattern, Expression)] -> StepResult
findCase v = foldr f (throwError "no matching cases")
  where
    f :: (Pattern, Expression) -> StepResult -> StepResult
    f (p, e) acc = case patternMatch v p of
      Left _ -> acc
      Right ss -> return $ foldr (🔥) e ss