{-# LANGUAGE RecursiveDo #-}

module Eval where

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
import Types

type Environment = Map Variable Value

type StepResult = Either String (Either (Environment, Expression) Value)

data Value
  = IntVal Int
  | BoolVal Bool
  | -- note! function values can go wrong when they are run
    FunVal (Value -> StepResult)
  | FunVal1 (Value -> Expression)
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
  show (FunVal _) = "<function>" -- can't show functions

-- empty map
empty :: Environment
empty = Map.empty

vLookup :: Variable -> Map Variable Value -> StepResult
vLookup x env =
  case Map.lookup x env of
    Just ty -> return $ return ty
    Nothing -> throwError $ "Unbound variable " ++ x

retVal :: Value -> StepResult
retVal = return . return

retStep :: Expression -> Environment -> StepResult
retStep e env = return $ Left (env, e)

isErr :: Either a b -> Bool
isErr (Left _) = True
isErr (Right _) = False

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

evalBounded (Var x) s = vLookup x s
evalBounded (IntExp i) _ = retVal $ IntVal i
evalBounded (BoolExp i) _ = retVal $ BoolVal i
evalBounded (Op o e1 e2) s = do
  t1 <- evalBounded e1 s
  t2 <- evalBounded e2 s
  case (t1, t2) of
    (Left (s', e1'), _) -> retStep (Op o e1' e2) s' -- step evaluator
    (Right _, Left (s', e2')) -> retStep (Op o e1 e2') s'
    (Right v1, Right v2) -> evalB o v1 v2 s
-- lamdba function: new version just returns same thing

evalBounded (Lam x e) s = retVal $ FunVal (\v -> return $ Left (Map.insert x v s, e))
-- Function Application:
-- no arguments
evalBounded (App lam []) s = retStep lam s
-- Applied to data constructor
evalBounded (App (C dt) (x : xs)) s = do
  t1 <- evalBounded x s
  case t1 of
    Left (s', x') -> retStep (App (C dt) (x' : xs)) s'
    Right _ -> retStep (App (PC dt [x]) xs) s
-- Applied to already partially applied data constructor
evalBounded (App (PC dt l) (x : xs)) s = do
  t1 <- evalBounded x s
  case t1 of
    Left (s', x') -> retStep (App (PC dt l) (x' : xs)) s'
    Right _ -> retStep (App (PC dt (l ++ [x])) xs) s
-- Applied to normal functions/everything else
evalBounded (App lam (x : xs)) s = do
  t1 <- evalBounded lam s
  t2 <- evalBounded x s
  case (t1, t2) of
    (Left (s', lam'), _) -> retStep (App lam' (x : xs)) s'
    (_, Left (s', x')) -> retStep (App lam (x' : xs)) s'
    (Right (FunVal g), Right v) -> case g v of
      Left _ -> g v -- threw an error
      Right (Left (s', lam')) -> return $ Left (s', App lam' xs) -- apply function one round
      _ -> throwError "app requires a function/data constructor"
    _ -> throwError "app requires a function"
-- Let Statements
evalBounded (Let x e1 e2) s = mdo
  t <- evalBounded e1 s
  case t of
    Left (s'', e1') -> return $ Left (s'', Let x e1' e2)
    Right v -> do
      let s' = Map.insert x v s
      return $ Left (s', e2)
evalBounded (Annot e _) s = retStep e s
evalBounded (C dt) _ = retVal $ UserDT dt []
-- Evaluated user defined type evaluated to some arguments
evalBounded (PC dt l) s = retVal $ UserDT dt l'
  where
    l' =
      Prelude.foldr
        ( \x acc -> case evalBounded x s of
            Right (Right v) -> v : acc
            _ -> acc
        )
        []
        l

-- if statements
evalBounded (If cond e2 e3) s = do
  t <- evalBounded cond s
  case t of
    Left (s'', cond') -> retStep (If cond' e2 e3) s''
    Right (BoolVal b) -> if b then retStep e2 s else retStep e3 s
    _ -> throwError "cannot evaluate non-bool in if statement"
-- case
evalBounded (Case e1 ps) s = do
  t1 <- evalBounded e1 s
  case t1 of
    Left (s', e1') -> retStep (Case e1' ps) s'
    Right v -> findCase v ps s

patternMatch :: Value -> Pattern -> Environment -> (Bool, Environment)
patternMatch (IntVal i) (IntP p) s = (i == p, s)
patternMatch (BoolVal b) (BoolP p) s = (b == p, s)
patternMatch v (VarP x) s = (True, Map.insert x v s)
patternMatch (UserDT dt l) (P dt' ps) s =
  if getDCName dt == getDCName dt' && length l == length ps
    then
      Prelude.foldr
        ( \(v, p) acc ->
            let res = patternMatch v p (snd acc)
             in (fst res && fst acc, snd res)
        )
        (True, s)
        (zip l ps)
    else (False, s)
patternMatch _ _ s = (False, s)

checkCase :: Value -> (Pattern, Expression) -> Environment -> StepResult
checkCase v (p, e) s =
  let (res, s') = patternMatch v p s
   in if res
        then retStep e s'
        else throwError "case match invalid"

findCase :: Value -> [(Pattern, Expression)] -> Environment -> StepResult
findCase v l s = Prelude.foldr f (throwError "no matching cases") l
  where
    f :: (Pattern, Expression) -> StepResult -> StepResult
    f c acc =
      let res = checkCase v c s
       in if isErr res then acc else res

-- //TODO add user defined constructors

eval :: Expression -> Environment -> Either String Value
eval e s = do
  step <- evalBounded e s
  case step of
    Left (s', e') -> eval e' s'
    Right v -> return v

-- -- repl

-- test cases:

-- replE :: IO ()
-- replE = do
--   putStr "%> "
--   line <- getLine
--   case Parser.parse line of
--     Just exp ->
--       case eval exp Map.empty of
--         Left str -> putStrLn str >> replE
--         Right val -> putStrLn (show val) >> replE
--     Nothing -> putStrLn "what?!?" >> replE

-- -- TEST CASES
isFailing :: Either a b -> Test
isFailing (Left _) = TestCase $ assert True
isFailing (Right _) = TestCase $ assert False

{-
==========================================================
Potential Second Attempt at Eval that isn't gross

==========================================================
-}
type StepResult1 = Either String Step

-- opt'ing to use variables -> expressions to avoid back and forth conversions
-- between expressions and values on lookup
type Environment1 = Map Variable Expression

data Step = Step {getExpr :: Expression, getEnv :: Environment1}

-- takes a basically eval'd function and tries to eval the operator
evalB' :: Bop -> Expression -> Expression -> Environment1 -> StepResult1
evalB' Plus (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 + i2)) s
evalB' Minus (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 - i2)) s
evalB' Times (IntExp i1) (IntExp i2) s = return $ Step (IntExp (i1 * i2)) s
evalB' Gt (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 > i2)) s
evalB' Ge (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 >= i2)) s
evalB' Lt (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 < i2)) s
evalB' Le (IntExp i1) (IntExp i2) s = return $ Step (BoolExp (i1 <= i2)) s
evalB' _ _ _ _ = throwError "Invalid argument to binary operator"

convertValToExpr :: Value -> Expression
convertValToExpr = undefined

vLookup' :: Variable -> Environment1 -> StepResult1
vLookup' x env =
  case Map.lookup x env of
    Just ty -> return $ Step ty env
    Nothing -> throwError $ "Unbound variable " ++ x

isValue :: Expression -> Bool
isValue (IntExp _) = True
isValue (BoolExp _) = True
isValue (Lam _ _) = True
isValue (C _) = True
isValue (PC _ _) = True
isValue _ = False

convertToValue :: Expression -> Either String Value
convertToValue (IntExp i) = return $ IntVal i
convertToValue (BoolExp b) = return $ BoolVal b
convertToValue (Lam v exp) = return $ FunVal1 (const exp)
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

evalBounded' :: Expression -> Environment1 -> StepResult1
evalBounded' (Var x) env = vLookup' x env
evalBounded' exp@(IntExp _) env = return $ Step exp env
evalBounded' exp@(BoolExp _) env = return $ Step exp env
evalBounded' (Op o e1 e2) env = do
  s <- evalBounded' e1 env
  s2 <- evalBounded' e2 env
  if isValue (getExpr s) && isValue (getExpr s2)
    then evalB' o (getExpr s) (getExpr s2) env
    else return $ Step (Op o (getExpr s) (getExpr s2)) env
evalBounded' exp@(Lam _ _) env = return $ Step exp env
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
  let env' = Map.insert v (getExpr s) (getEnv s)
   in if isValue (getExpr s)
        then return $ Step e2 env'
        else return $ Step (getExpr s) env'

-- -- Converting case statements
evalBounded' (Case e1 ps) env = do
  s <- evalBounded' e1 env
  if isValue $ getExpr s
    then findCase' (getExpr s) ps env
    else return $ Step (Case (getExpr s) ps) (getEnv s)

patternMatch' :: Expression -> Pattern -> Environment1 -> (Bool, Environment1)
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

checkCase' :: Expression -> (Pattern, Expression) -> Environment1 -> StepResult1
checkCase' v (p, e) s =
  let (res, s') = patternMatch' v p s
   in if res
        then return $ Step e s'
        else throwError "case match invalid"

findCase' :: Expression -> [(Pattern, Expression)] -> Environment1 -> StepResult1
findCase' v l s = Prelude.foldr f (throwError "no matching cases") l
  where
    f :: (Pattern, Expression) -> StepResult1 -> StepResult1
    f c acc =
      let res = checkCase' v c s
       in if isErr res then acc else res

eval' :: Expression -> Environment1 -> Either String Value
eval' e env = do
  step <- evalBounded' e env
  if isValue (getExpr step)
    then convertToValue (getExpr step)
    else eval' (getExpr step) (getEnv step)

topeval :: FilePath -> IO ()
topeval fs = do
  exp <- parseFile fs
  print exp
  let res = eval' exp Map.empty
  print res

{-
===================================================
                    Tests
===================================================
-}

testsFailing =
  TestList
    [ "1 + true" ~: isFailing $ eval' (Op Plus (IntExp 1) (BoolExp True)) Map.empty,
      "1 1" ~: isFailing $ eval' (App (IntExp 1) [IntExp 1]) Map.empty,
      "if 1 .." ~: isFailing $ eval' (Case (IntExp 1) [(BoolP False, IntExp 3)]) Map.empty,
      "X" ~: isFailing $ eval' (Var "X") Map.empty
    ]

fun1 = Lam "y" (Op Plus (Var "y") (IntExp 1))

fun2 = Lam "y" (Lam "z" (Op Minus (Var "y") (Var "z")))

testLet =
  TestList
    [ "let x = 5 in x" ~: eval' (Let "x" (IntExp 5) (Var "x")) Map.empty ~?= Right (IntVal 5),
      "let x = 5 in x + 1"
        ~: eval' (Let "x" (IntExp 5) (Op Plus (Var "x") (IntExp 1))) Map.empty ~?= Right (IntVal 6),
      "let x = y -> y + 1 in x 3"
        ~: eval' (Let "x" fun1 (App (Var "x") [IntExp 3])) Map.empty ~?= Right (IntVal 4),
      "let x = y -> y + 1 in x 3 4"
        ~: isFailing
        $ eval' (Let "x" fun1 (App (Var "x") [BoolExp True, IntExp 4])) Map.empty,
      "let x = y z -> y - z in x 3 4"
        ~: eval' (Let "x" fun2 (App (Var "x") [IntExp 3, IntExp 4])) Map.empty ~?= Right (IntVal (-1)),
      "let x = y z -> y - z in x True 5"
        ~: isFailing
        $ eval' (Let "x" fun2 (App (Var "x") [BoolExp True, IntExp 5])) Map.empty
    ]

case1 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5), (VarP "y", Var "y")]

case2 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5)]

testCasingSimple =
  TestList
    [ "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 3"
        ~: eval' case1 (Map.insert "x" (IntExp 3) Map.empty) ~?= Right (IntVal 3),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 6"
        ~: eval' case1 (Map.insert "x" (IntExp 6) Map.empty) ~?= Right (IntVal 6),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = True"
        ~: eval' case1 (Map.insert "x" (BoolExp True) Map.empty) ~?= Right (IntVal 5),
      "case x of [3 -> 4, True -> 5] where x = 6"
        ~: isFailing
        $ eval' case2 (Map.insert "x" (IntExp 6) Map.empty)
    ]

testUserDefined =
  TestList
    [ "let x = P in x"
        ~: eval' (Let "x" (C (DC "P" IntTy)) (Var "x")) Map.empty ~?= Right (UserDT (DC "P" IntTy) []),
      "let x = P 3 4 in x"
        ~: eval' (Let "x" (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4]) (Var "x")) Map.empty ~?= Right (UserDT (DC "P" IntTy) [IntVal 3, IntVal 4])
    ]

testFunctions =
  TestList
    [ "let x = a -> b -> a + b in x 4 5"
        ~: eval' (Let "x" (Lam "a" (Lam "b" (Op Plus (Var "a") (Var "b")))) (App (Var "x") [IntExp 4, IntExp 5])) Map.empty ~?= Right (IntVal 9)
    ]

-- -- quickcheck property
-- -- Can be evaluated property
isValid :: Expression -> Bool
isValid = const True

prop_stepExec :: Expression -> Property
prop_stepExec e =
  isValid e ==> not (isErr x)
  where
    x = evalBounded e Map.empty

quickCheckN :: Test.QuickCheck.Testable prop => Int -> prop -> IO ()
quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n, maxSize = 100}

tests :: IO ()
tests = do
  _ <-
    runTestTT
      ( TestList
          [testsFailing, testLet, testCasingSimple, testUserDefined, testFunctions]
      )
  return ()