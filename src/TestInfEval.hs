{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TestInfEval where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Either (isLeft, isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vec.Lazy (Vec (VNil, (:::)))
import Eval
import Generators
import Parser
import Test.HUnit
  ( Assertable (assert),
    Test (TestCase, TestList),
    runTestTT,
    (~:),
    (~?=),
  )
import Test.QuickCheck
import TypeInf
import Types

-- // TODO: allow for type variables
{-
===================================================
                Eval Unit Tests
===================================================
-}

isFailing :: Either a b -> Test
isFailing (Left _) = TestCase $ assert True
isFailing (Right _) = TestCase $ assert False

testsFailing =
  TestList
    [ "1 + true" ~: isFailing $ eval (Op Plus (IntExp 1) (BoolExp True)),
      "1 1" ~: isFailing $ eval (App (IntExp 1) [IntExp 1]),
      "if 1 .." ~: isFailing $ eval (Case (IntExp 1) [(BoolP False, IntExp 3)]),
      "X" ~: isFailing $ eval (Var "X")
    ]

fun1 = Lam "y" (Op Plus (Var "y") (IntExp 1))

fun2 = Lam "y" (Lam "z" (Op Minus (Var "y") (Var "z")))

testLet =
  TestList
    [ "let x = 5 in x" ~: eval (Let "x" (IntExp 5) (Var "x")) ~?= Right (IntExp 5),
      "let x = 5 in x + 1"
        ~: eval (Let "x" (IntExp 5) (Op Plus (Var "x") (IntExp 1))) ~?= Right (IntExp 6),
      "let x = y -> y + 1 in x 3"
        ~: eval (Let "x" fun1 (App (Var "x") [IntExp 3])) ~?= Right (IntExp 4),
      "let x = y -> y + 1 in x 3 4"
        ~: isFailing
        $ eval (Let "x" fun1 (App (Var "x") [BoolExp True, IntExp 4])),
      "let x = y z -> y - z in x 3 4"
        ~: eval (Let "x" fun2 (App (Var "x") [IntExp 3, IntExp 4])) ~?= Right (IntExp (-1)),
      "let x = y z -> y - z in x True 5"
        ~: isFailing
        $ eval (Let "x" fun2 (App (Var "x") [BoolExp True, IntExp 5]))
    ]

case1 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5), (VarP "y", Var "y")]

case2 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5)]

testCasing =
  TestList
    [ "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 3"
        ~: eval (Let "x" (IntExp 3) case1) ~?= Right (IntExp 3),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 6"
        ~: eval (Let "x" (IntExp 6) case1) ~?= Right (IntExp 6),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = True"
        ~: eval (Let "x" (BoolExp True) case1) ~?= Right (IntExp 5),
      "case x of [3 -> 4, True -> 5] where x = 6"
        ~: isFailing
        $ eval (Let "x" (IntExp 6) case2)
    ]

if1 = If (BoolExp True) (IntExp 3) (IntExp 4)

-- unsimplified expression
if2 = If (Op Le (IntExp 3) (IntExp 5)) (BoolExp True) (BoolExp False)

testIfs =
  TestList
    [ "if true then 3 else 4"
        ~: eval if1 ~?= Right (IntExp 3),
      "if (3 < 5) then True else False"
        ~: eval if2 ~?= Right (BoolExp True),
      "let x = if true then 3 else 4 in x (test let binding to ifs)"
        ~: eval (Let "x" if2 (Var "x")) ~?= Right (BoolExp True)
    ]

testUserDefined =
  TestList
    [ "let x = P in x"
        ~: eval (Let "x" (C (DC "P" IntTy)) (Var "x")) ~?= Right (C (DC "P" IntTy)),
      "let x = P 3 4 in x"
        ~: eval (Let "x" (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4]) (Var "x")) ~?= Right (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4])
    ]

testFunctions :: Test
testFunctions =
  TestList
    [ "let x = a -> b -> a + b in x 4 5"
        ~: eval (Let "x" (Lam "a" (Lam "b" (Op Plus (Var "a") (Var "b")))) (App (Var "x") [IntExp 4, IntExp 5])) ~?= Right (IntExp 9),
      "let y = 3 in let x = a -> y in x 4 (simple lexical scoping test)"
        ~: eval (Let "y" (IntExp 3) (Let "x" (Lam "a" (Var "y")) (App (Var "x") [IntExp 4]))) ~?= Right (IntExp 3),
      "let y = 3 in let x = a -> y in let y = 17 in x 4 (complex lexical scoping test)"
        ~: eval (Let "y" (IntExp 3) (Let "x" (Lam "a" (Var "y")) (Let "y" (IntExp 17) (App (Var "x") [IntExp 4])))) ~?= Right (IntExp 3)
    ]

-- TYPE INF

good1 = Let "f" (Lam "x" (var "x")) (App (Var "f") [IntExp 1])

-- test constraint solving:
-- let f = \x -> x + 1 in (f 1)
good2 = Let "f" (Lam "x" (Op Plus (var "x") (IntExp 1))) (App (Var "f") [IntExp 1])

-- test Spine based application
-- (\x,y -> x + y) 1 2
good3 = App (Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1, IntExp 2]

-- test polymorphism
-- let f = \x -> x in let a = f True in f 1
good4 = Let "f" (Lam "x" (App (Var "x") [])) (Let "a" (App (Var "f") [IntExp 1]) (App (Var "f") [BoolExp True]))

-- partial application
-- (\x, y -> x + y) 1
good5 = App (Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1]

-- BAD CASES
-- bad operator parameters
bad1 = Op Plus (IntExp 1) (BoolExp True)

-- wrong shape
bad2 = App (Lam "x" (Op Plus (var "x") (IntExp 1))) [IntExp 1, IntExp 2]

-- Polymorphic cases (see files with the same names for original)
-- I didn't include all of them here because it's kind of hard to say what the exact type
-- of the polymorphic type will be (because of name differences)
exCompose = Let "compose" (Annot (Lam "f" (Lam "g" (Lam "x" (App (Var "f") [App (Var "g") [Var "x"]])))) (Forall "abc" (FunTy (FunTy (VarTy 'b') (VarTy 'c')) (FunTy (FunTy (VarTy 'a') (VarTy 'b')) (FunTy (VarTy 'a') (VarTy 'c')))))) (Let "id" (Annot (Lam "x" (Var "x")) (Forall "a" (FunTy (VarTy 'a') (VarTy 'a')))) (Let "auto" (Annot (App (Var "id") [Var "id"]) (FunTy (Forall "a" (FunTy (VarTy 'a') (VarTy 'a'))) (Forall "b" (FunTy (VarTy 'b') (VarTy 'b'))))) (App (Var "compose") [Var "auto", Var "auto", Var "id", IntExp 1])))

exRanked = Let "f" (Annot (Lam "x" (App (C (DC {getDCName = "Both", getType = Forall "ab" (FunTy (VarTy 'a') (FunTy (VarTy 'b') (TyCstr (TC "Both" (SS (SS SZ))) (VarTy 'a' ::: VarTy 'b' ::: VNil))))})) [App (Var "x") [IntExp 1], App (Var "x") [BoolExp True]])) (FunTy (Forall "a" (FunTy (VarTy 'a') (VarTy 'a'))) (TyCstr (TC "Both" (SS (SS SZ))) (IntTy ::: BoolTy ::: VNil)))) (App (Var "f") [Lam "x" (Var "x")])

tyRanked = TyCstr (TC "Both" (SS (SS (SZ)))) (IntTy ::: BoolTy ::: VNil)

testTypeInf =
  TestList
    [ -- good
      typeInference emptyEnv good1 ~?= Right IntTy,
      typeInference emptyEnv good2 ~?= Right IntTy,
      typeInference emptyEnv good3 ~?= Right IntTy,
      typeInference emptyEnv good4 ~?= Right BoolTy,
      typeInference emptyEnv good5 ~?= Right (FunTy IntTy IntTy),
      -- bad
      isLeft (typeInference emptyEnv bad1) ~?= True,
      isLeft (typeInference emptyEnv bad2) ~?= True,
      -- poly
      typeInference emptyEnv exCompose ~?= Right IntTy,
      typeInference emptyEnv exRanked ~?= Right tyRanked
    ]

{-
===================================================
      Type Inf and Eval QuickCheck Properties
===================================================
-}

-- | if an expression is well typed, then it is either a value or it steps
progress :: Expression -> Property
progress e = isValid e ==> isValue e || isRight (step e)

-- | if an expression is well typed and not a value
-- then its type is preserved after a step
preservation :: Expression -> Property
preservation e =
  -- if: e is well typed and not a value
  isValid e && not (isValue e)
    ==> isRight
    $ do
      -- infer starting type
      ty1 <- typeInference emptyEnv e
      -- take a step
      e' <- step e
      -- check that the expression can still be *checked* to have the same type
      let tc = checkType emptyEnv e' ty1
      runTc tc

{-
This was our first attempt at preservation. It fails for two reasons.
1) Stepping removes annotations, which can change the type (either by making it more general,
  or not being to infer the type at all since annotations provide local information)
2) Stepping an 'if' or a 'case' cane make the type more general because we might step to
  a branch with a more general type than the overall expression. For example:

    if True then \x -> x else \y -> y + 1

  This starts with type Int -> Int but steps to type forall a . a -> a
 -}
preservationBad :: Expression -> Property
preservationBad e =
  -- if: e is well typed and not a value
  isValid e && not (isValue e)
    ==> let -- starting type
            ty1 = typeInference emptyEnv e
            -- type post step
            ty2 = do
              e' <- step e
              typeInference emptyEnv e'
         in -- then: types must be alpha equivalent
            case (ty1, ty2) of
              (Right ty1', Right ty2') -> isRight $ alphaEquiv ty1' ty2'
              _ -> False

quickCheckN :: (Testable prop) => Int -> prop -> IO ()
quickCheckN n = quickCheck . withMaxSuccess n

tests :: IO ()
tests = do
  _ <-
    runTestTT
      ( TestList
          [testsFailing, testLet, testCasing, testIfs, testUserDefined, testFunctions, testTypeInf]
      )
  quickCheck progress
  quickCheck preservation