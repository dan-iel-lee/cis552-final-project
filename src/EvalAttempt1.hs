{-# LANGUAGE RecursiveDo #-}

module EvalAttempt1 where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Map as Map
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

data Value
  = IntVal Int
  | BoolVal Bool
  | FunVal Variable Expression
  | UserDT DataConstructor [Value]

instance Eq Value where
  IntVal i == IntVal j = i == j
  BoolVal i == BoolVal j = i == j
  UserDT dt l == UserDT dt' l' =
    getDCName dt == getDCName dt'
      && length l == length l'
      && Prelude.foldr (\(v1, v2) acc -> v1 == v2 && acc) True (zip l l')
  FunVal v exp == FunVal v' exp' = v == v' && exp == exp'
  _ == _ = False

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (UserDT dt l) = getDCName dt ++ " " ++ Prelude.foldr (\x acc -> show x ++ " " ++ acc) [] l
  show (FunVal v exp) = "(\\" ++ v ++ "->" ++ show exp ++ ")"

{-
==========================================================

     Potential Second Attempt at Eval that isn't gross

==========================================================
-}
-- opt'ing to use variables -> expressions to avoid back and forth conversions
-- between expressions and values on lookup
type Environment = Map Variable Expression

data Step = Step {getExpr :: Expression, getEnv :: Environment}

type StepResult = Either String Step

-- data ScopedExpression
--   = Exp Expression
--   | Fun Expression Environment

instance Show Step where
  show (Step expr env) = "Expr: " ++ show expr ++ "\n" ++ "Map: " ++ show env

isErr :: Either a b -> Bool
isErr (Left _) = True
isErr _ = False

isValue :: Expression -> Bool
isValue (IntExp _) = True
isValue (BoolExp _) = True
isValue (Lam _ _) = True
isValue (C _) = True
isValue (PC _ _) = True
isValue _ = False

-- | Converts an expression to a "value"; we really don't need this type anymore actually
convertToValue :: Expression -> Either String Value
convertToValue (IntExp i) = return $ IntVal i
convertToValue (BoolExp b) = return $ BoolVal b
convertToValue (Lam v exp) = return $ FunVal v exp
convertToValue (C dt) = return $ UserDT dt []
convertToValue (PC dt l) = Prelude.foldr convertArg (return $ UserDT dt []) l
  where
    convertArg :: Expression -> Either String Value -> Either String Value
    convertArg e (Right (UserDT dt l)) =
      case convertToValue e of
        Left x -> throwError x
        Right v -> return $ UserDT dt (v : l)
    convertArg _ _ = throwError "could not directly convert expression to value"
convertToValue _ = throwError "could not directly convert expression to value"

-- | Tries to look up variable from environment
vLookup' :: Variable -> Environment -> StepResult
vLookup' x env =
  case Map.lookup x env of
    Just ty -> return $ Step ty env
    Nothing -> throwError $ "Unbound variable " ++ x

-- takes a basically eval'd function and tries to eval the operator
evalB' :: Bop -> Expression -> Expression -> Environment -> StepResult
evalB' Plus (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 + i2)) s
evalB' Minus (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 - i2)) s
evalB' Times (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 * i2)) s
evalB' Gt (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 > i2)) s
evalB' Ge (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 >= i2)) s
evalB' Lt (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 < i2)) s
evalB' Le (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 <= i2)) s
evalB' _ _ _ _ = throwError "Invalid argument to binary operator"

-- | This is the main function used to evaluate a single "step" in a given expression
-- | Returns back the same expression if it couldn't be simplified further.
evalBounded' :: Expression -> Environment -> StepResult
-- stepping primitives + operators
evalBounded' (Var x) env = vLookup' x env
evalBounded' exp@(IntExp _) env = return $ Step exp env
evalBounded' exp@(BoolExp _) env = return $ Step exp env
evalBounded' (Op o e1 e2) env = do
  s <- evalBounded' e1 env
  s2 <- evalBounded' e2 env
  if isValue (getExpr s) && isValue (getExpr s2)
    then evalB' o (getExpr s) (getExpr s2) env
    else return $ Step (Op o (getExpr s) (getExpr s2)) env

-- -- Converting Type Annotations
evalBounded' (Annot exp _) env = return $ Step exp env
-- -- Converting lambda's
evalBounded' exp@(Lam _ _) env = return $ Step exp env
-- -- Converting if statements
evalBounded' (If cond e1 e2) env = do
  s <- evalBounded' cond env
  if isValue $ getExpr s
    then case getExpr s of
      BoolExp b -> return $ Step (if b then e1 else e2) env
      _ -> throwError "cannot evaluate non-bool in if statement"
    else return $ Step (getExpr s) (getEnv s)

-- -- Converting Function Application Calls
evalBounded' (App l@(Lam v f) (e : es)) env = do
  s <- evalBounded' e env
  if isValue (getExpr s)
    then return $ Step (App f es) (Map.insert v (getExpr s) (getEnv s))
    else return $ Step (App l (getExpr s : es)) (getEnv s)

-- -- Converting User Def Types
evalBounded' udt@(C _) env = return $ Step udt env
evalBounded' (App udt@(C _) []) env = return $ Step udt env
evalBounded' (App udt@(C dt) (e : es)) env = do
  s <- evalBounded' e env
  if isValue (getExpr s)
    then return $ Step (App (PC dt [getExpr s]) es) (getEnv s)
    else return $ Step (App udt (getExpr s : es)) (getEnv s)
evalBounded' (App udt@(PC dt l) (e : es)) env = do
  s <- evalBounded' e env
  if isValue (getExpr s)
    then return $ Step (App (PC dt (l ++ [getExpr s])) es) (getEnv s)
    else return $ Step (App udt (getExpr s : es)) (getEnv s)
-- -- Converting empty lambda calls
evalBounded' (App l []) env = return $ Step l env
-- -- Finally handle unsimplified function applications
evalBounded' (App f es) env =
  if isValue f && not (Prelude.null es)
    then throwError "cannot apply to non-function"
    else do
      s <- evalBounded' f env
      return $ Step (App (getExpr s) es) env

-- -- Converting let statements
evalBounded' (Let v e e2) env = mdo
  s <- evalBounded' e env
  let env' = Map.insert v (getExpr s) env
  if isValue (getExpr s)
    then return $ Step e2 env'
    else return $ Step (Let v (getExpr s) e2) (getEnv s)

-- -- Converting case statements
evalBounded' (Case e1 ps) env = do
  s <- evalBounded' e1 env
  if isValue $ getExpr s
    then findCase' (getExpr s) ps env
    else return $ Step (Case (getExpr s) ps) (getEnv s)

-- | Does the work of matching expressions against patterns.
--  Returns a tuple x environment since variable matches may change the environment
patternMatch' :: Expression -> Pattern -> Environment -> (Bool, Environment)
patternMatch' (IntExp i) (IntP p) s = (i == p, s)
patternMatch' (BoolExp b) (BoolP p) s = (b == p, s)
patternMatch' e (VarP x) s = (True, Map.insert x e s)
patternMatch' (C dt) (P dt' []) s = (getDCName dt == getDCName dt', s)
patternMatch' (PC dt l) (P dt' ps) s =
  if getDCName dt == getDCName dt' && length l == length ps
    then
      Prelude.foldr
        ( \(v, p) acc ->
            let res = patternMatch' v p (snd acc)
             in (fst res && fst acc, snd res)
        )
        (True, s)
        (zip l ps)
    else (False, s)
patternMatch' _ _ s = (False, s)

-- | Checks a specific case and returns the next step if it matched
checkCase' :: Expression -> (Pattern, Expression) -> Environment -> StepResult
checkCase' v (p, e) s =
  let (res, s') = patternMatch' v p s
   in if res
        then return $ Step e s'
        else throwError "case match invalid"

-- | Searches through all cases, and tries to match against a simplified expression
findCase' :: Expression -> [(Pattern, Expression)] -> Environment -> StepResult
findCase' v l s = Prelude.foldr f (throwError "no matching cases") l
  where
    f :: (Pattern, Expression) -> StepResult -> StepResult
    f c acc =
      let res = checkCase' v c s
       in if isErr res then acc else res

-- | Evaluates <= n steps in the expression
evalStep :: Expression -> Environment -> Int -> StepResult
evalStep e env 0 = return $ Step e env
evalStep e env i = do
  step <- evalBounded' e env
  if isValue (getExpr step) || i <= 0
    then return $ Step (getExpr step) (getEnv step)
    else evalStep (getExpr step) (getEnv step) (i -1)

-- | Evaluates (or tries to evaluate) to completion
eval :: Expression -> Environment -> Either String Value
eval e env = do
  step <- evalBounded' e env
  if isValue (getExpr step)
    then convertToValue (getExpr step)
    else eval (getExpr step) (getEnv step)

-- | Takes in a file, prints the result of evaluation after parsing
topEval :: FilePath -> IO ()
topEval fs = do
  exp <- parseFile fs
  --print exp
  let res = eval exp Map.empty
  print res

-- | Takes in a file, parses expression, and prints the State and Expression of
-- evaluation of <= n steps
topEvalBounded :: FilePath -> Int -> IO ()
topEvalBounded fs i = do
  exp <- parseFile fs
  let res = evalStep exp Map.empty i
  print res