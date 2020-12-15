module Tests where

import qualified Eval as E
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

{-
===================================================
                    Tests
===================================================
-}

isFailing :: Either a b -> Test
isFailing (Left _) = TestCase $ assert True
isFailing (Right _) = TestCase $ assert False

testsFailing =
  TestList
    [ "1 + true" ~: isFailing $ E.eval (Op Plus (IntExp 1) (BoolExp True)),
      "1 1" ~: isFailing $ E.eval (App (IntExp 1) [IntExp 1]),
      "if 1 .." ~: isFailing $ E.eval (Case (IntExp 1) [(BoolP False, IntExp 3)]),
      "X" ~: isFailing $ E.eval (Var "X")
    ]

fun1 = Lam "y" (Op Plus (Var "y") (IntExp 1))

fun2 = Lam "y" (Lam "z" (Op Minus (Var "y") (Var "z")))

testLet =
  TestList
    [ "let x = 5 in x" ~: E.eval (Let "x" (IntExp 5) (Var "x")) ~?= Right (IntExp 5),
      "let x = 5 in x + 1"
        ~: E.eval (Let "x" (IntExp 5) (Op Plus (Var "x") (IntExp 1))) ~?= Right (IntExp 6),
      "let x = y -> y + 1 in x 3"
        ~: E.eval (Let "x" fun1 (App (Var "x") [IntExp 3])) ~?= Right (IntExp 4),
      "let x = y -> y + 1 in x 3 4"
        ~: isFailing
        $ E.eval (Let "x" fun1 (App (Var "x") [BoolExp True, IntExp 4])),
      "let x = y z -> y - z in x 3 4"
        ~: E.eval (Let "x" fun2 (App (Var "x") [IntExp 3, IntExp 4])) ~?= Right (IntExp (-1)),
      "let x = y z -> y - z in x True 5"
        ~: isFailing
        $ E.eval (Let "x" fun2 (App (Var "x") [BoolExp True, IntExp 5]))
    ]

case1 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5), (VarP "y", Var "y")]

case2 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5)]

testCasing =
  TestList
    [ "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 3"
        ~: E.eval (Let "x" (IntExp 3) case1) ~?= Right (IntExp 3),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 6"
        ~: E.eval (Let "x" (IntExp 6) case1) ~?= Right (IntExp 6),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = True"
        ~: E.eval (Let "x" (BoolExp True) case1) ~?= Right (IntExp 5),
      "case x of [3 -> 4, True -> 5] where x = 6"
        ~: isFailing
        $ E.eval (Let "x" (IntExp 6) case2)
    ]

if1 = If (BoolExp True) (IntExp 3) (IntExp 4)

-- unsimplified expression
if2 = If (Op Le (IntExp 3) (IntExp 5)) (BoolExp True) (BoolExp False)

testIfs =
  TestList
    [ "if true then 3 else 4"
        ~: E.eval if1 ~?= Right (IntExp 3),
      "if (3 < 5) then True else False"
        ~: E.eval if2 ~?= Right (BoolExp True),
      "let x = if true then 3 else 4 in x (test let binding to ifs)"
        ~: E.eval (Let "x" if2 (Var "x")) ~?= Right (BoolExp True)
    ]

testUserDefined =
  TestList
    [ "let x = P in x"
        ~: E.eval (Let "x" (C (DC "P" IntTy)) (Var "x")) ~?= Right (C (DC "P" IntTy)),
      "let x = P 3 4 in x"
        ~: E.eval (Let "x" (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4]) (Var "x")) ~?= Right (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4])
    ]

testFunctions :: Test
testFunctions =
  TestList
    [ "let x = a -> b -> a + b in x 4 5"
        ~: E.eval (Let "x" (Lam "a" (Lam "b" (Op Plus (Var "a") (Var "b")))) (App (Var "x") [IntExp 4, IntExp 5])) ~?= Right (IntExp 9),
      "let y = 3 in let x = a -> y in x 4 (simple lexical scoping test)"
        ~: E.eval (Let "y" (IntExp 3) (Let "x" (Lam "a" (Var "y")) (App (Var "x") [IntExp 4]))) ~?= Right (IntExp 3),
      "let y = 3 in let x = a -> y in let y = 17 in x 4 (complex lexical scoping test)"
        ~: E.eval (Let "y" (IntExp 3) (Let "x" (Lam "a" (Var "y")) (Let "y" (IntExp 17) (App (Var "x") [IntExp 4])))) ~?= Right (IntExp 3)
    ]

tests :: IO ()
tests = do
  _ <-
    runTestTT
      ( TestList
          [testsFailing, testLet, testCasing, testIfs, testUserDefined, testFunctions]
      )
  return ()