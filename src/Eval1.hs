{-# LANGUAGE RecursiveDo #-}

module Eval1 where

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

type Environment = Map Variable Value

data Step
  = Step {getExpr :: Expression, getEnv :: Environment}
  | Value {getVal :: Value}

type StepResult = Either String Step

data Value
  = IntVal Int
  | BoolVal Bool
  | -- note! function values can go wrong when they are run
    FunVal Variable (Value -> Step)
  | UserDT DataConstructor [Value]

instance Eq Value where
  IntVal i == IntVal j = i == j
  BoolVal i == BoolVal j = i == j
  UserDT dt l == UserDT dt' l' =
    getDCName dt == getDCName dt'
      && length l == length l'
      && Prelude.foldr (\(v1, v2) acc -> v1 == v2 && acc) True (zip l l')
  _ == _ = False

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (UserDT dt l) = getDCName dt ++ " " ++ Prelude.foldr (\x acc -> show x ++ " " ++ acc) [] l
  show (FunVal v f) = "(\\" ++ v ++ " -> " ++ show (getExpr (f (BoolVal True))) ++ ")"

instance Show Step where
  show (Step expr env) = "Expr: " ++ show expr ++ "\n" ++ "Map: " ++ show env ++ "\n"
  show (Value v) = show v

-- empty map
emptyEnv :: Environment
emptyEnv = Map.empty

retVal :: Value -> StepResult
retVal = return . Value

retStep :: Expression -> Environment -> StepResult
retStep e env = return $ Step e env

isErr :: Either a b -> Bool
isErr (Left _) = True
isErr (Right _) = False

isValue :: Step -> Bool
isValue (Value _) = True
isValue _ = False

vLookup :: Variable -> Map Variable Value -> StepResult
vLookup x env =
  case Map.lookup x env of
    Just ty -> retVal ty
    Nothing -> throwError $ "Unbound variable " ++ x

evalB :: Bop -> Value -> Value -> Environment -> StepResult
evalB Plus (IntVal i1) (IntVal i2) = retStep $ IntExp (i1 + i2)
evalB Minus (IntVal i1) (IntVal i2) = retStep $ IntExp (i1 - i2)
evalB Times (IntVal i1) (IntVal i2) = retStep $ IntExp (i1 * i2)
evalB Gt (IntVal i1) (IntVal i2) = retStep $ BoolExp (i1 > i2)
evalB Ge (IntVal i1) (IntVal i2) = retStep $ BoolExp (i1 >= i2)
evalB Lt (IntVal i1) (IntVal i2) = retStep $ BoolExp (i1 < i2)
evalB Le (IntVal i1) (IntVal i2) = retStep $ BoolExp (i1 <= i2)
evalB _ _ _ = const . throwError $ "Invalid argument to binary operator"

-- add val to environment helper

evalBounded :: Expression -> Environment -> StepResult
-- simple cases + operators

evalBounded (Var x) env = vLookup x env
evalBounded (IntExp i) _ = retVal $ IntVal i
evalBounded (BoolExp i) _ = retVal $ BoolVal i
evalBounded (Op o e e2) env = do
  s1 <- evalBounded e env
  s2 <- evalBounded e2 env
  case (s1, s2) of
    (Step e' env', _) -> retStep (Op o e' e2) env' -- step evaluator
    (_, Step e2' env') -> retStep (Op o e e2') env'
    (Value v, Value v2) -> evalB o v v2 env
-- lamdba function: new version just returns same thing

evalBounded (Lam x e) env = retVal $ FunVal x (\v -> Step e (Map.insert x v env))
-- Function Application:
-- no arguments
evalBounded (App lam []) env = retStep lam env
-- Applied to data constructor
evalBounded (App (C dt) (x : xs)) env = do
  s1 <- evalBounded x env
  case s1 of
    Step x' env' -> retStep (App (C dt) (x' : xs)) env'
    _ -> retStep (App (PC dt [x]) xs) env
-- Applied to already partially applied data constructor
evalBounded (App (PC dt l) (x : xs)) env = do
  s1 <- evalBounded x env
  case s1 of
    Step x' env' -> retStep (App (PC dt l) (x' : xs)) env'
    _ -> retStep (App (PC dt (l ++ [x])) xs) env
-- Applied to normal functions/everything else
evalBounded (App lam l@(e : es)) env = do
  t1 <- evalBounded lam env
  t2 <- evalBounded e env
  case (t1, t2) of
    (Step lam' env', _) -> retStep (App lam' l) env'
    (_, Step e' env') -> retStep (App lam (e' : es)) env'
    (Value (FunVal _ g), Value v) -> case g v of
      Step lam' env' -> retStep (App lam' es) env' -- apply function one round
      _ -> throwError "app requires a function/data constructor"
    _ -> throwError "app requires a function"
-- Let Statements
evalBounded (Let x e1 e2) env = mdo
  t <- evalBounded e1 env
  let env' = if isValue t then Map.insert x (getVal t) env else getEnv t
  case t of
    Step e1' _ -> retStep (Let x e1' e2) (Map.union env' env)
    Value _ -> retStep e2 (Map.union env' env)
evalBounded (Annot e _) env = retStep e env
evalBounded (C dt) _ = retVal $ UserDT dt []
-- Evaluated user defined type evaluated to some arguments
evalBounded (PC dt l) env = retVal $ UserDT dt l'
  where
    l' =
      Prelude.foldr
        ( \x acc -> case evalBounded x env of
            Right (Value v) -> v : acc
            _ -> acc
        )
        []
        l
-- case
evalBounded (Case e1 ps) env = do
  s <- evalBounded e1 env
  case s of
    Step e1' env' -> retStep (Case e1' ps) env'
    Value v -> findCase v ps env

patternMatch :: Value -> Pattern -> Environment -> (Bool, Environment)
patternMatch (IntVal i) (IntP p) env = (i == p, env)
patternMatch (BoolVal b) (BoolP p) env = (b == p, env)
patternMatch v (VarP x) env = (True, Map.insert x v env)
patternMatch (UserDT dt l) (P dt' ps) env =
  if getDCName dt == getDCName dt' && length l == length ps
    then
      Prelude.foldr
        ( \(v, p) acc ->
            let res = patternMatch v p (snd acc)
             in (fst res && fst acc, snd res)
        )
        (True, env)
        (zip l ps)
    else (False, env)
patternMatch _ _ env = (False, env)

checkCase :: Value -> (Pattern, Expression) -> Environment -> StepResult
checkCase v (p, e) env =
  let (res, env') = patternMatch v p env
   in if res
        then retStep e env'
        else throwError "case match invalid"

findCase :: Value -> [(Pattern, Expression)] -> Environment -> StepResult
findCase v l env = Prelude.foldr f (throwError "no matching cases") l
  where
    f :: (Pattern, Expression) -> StepResult -> StepResult
    f c acc =
      let res = checkCase v c env
       in if isErr res then acc else res

-- //TODO add user defined constructors

eval :: Expression -> Environment -> Either String Value
eval e env = do
  step <- evalBounded e env
  case step of
    Step e' env' -> eval e' env'
    Value v -> return v

-- evaluates for a certain number of steps
evalNum :: Expression -> Environment -> Int -> StepResult
evalNum e env num = do
  step <- evalBounded e env
  case step of
    Step e' env' -> if num <= 1 then retStep e' env' else evalNum e' env' (num - 1)
    Value v -> retVal v

-- | Takes in a file, prints the result of evaluation after parsing
topEval :: FilePath -> IO ()
topEval fs = do
  exp <- parseFile fs
  --print exp
  let res = eval exp Map.empty
  print res

-- | Evaluates <= n steps in the expression
evalStep :: Expression -> Environment -> Int -> StepResult
evalStep e env 0 = return $ Step e env
evalStep e env i = do
  step <- evalBounded e env
  if isValue step || i <= 0
    then return step
    else evalStep (getExpr step) (getEnv step) (i -1)

-- | Takes in a file, parses expression, and prints the State and Expression of
-- evaluation of <= n steps
topEvalBounded :: FilePath -> Int -> IO ()
topEvalBounded fs i = do
  exp <- parseFile fs
  let res = evalStep exp Map.empty i
  case res of
    Left err -> print err
    Right step -> print step