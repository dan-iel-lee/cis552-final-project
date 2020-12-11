module Tests where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Map as Map
import Data.Vec.Lazy (Vec (VNil))
import Eval
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
    [ "1 + true" ~: isFailing $ eval (Op Plus (IntExp 1) (BoolExp True)) Map.empty,
      "1 1" ~: isFailing $ eval (App (IntExp 1) [IntExp 1]) Map.empty,
      "if 1 .." ~: isFailing $ eval (Case (IntExp 1) [(BoolP False, IntExp 3)]) Map.empty,
      "X" ~: isFailing $ eval (Var "X") Map.empty
    ]

fun1 = Lam "y" (Op Plus (Var "y") (IntExp 1))

fun2 = Lam "y" (Lam "z" (Op Minus (Var "y") (Var "z")))

testLet =
  TestList
    [ "let x = 5 in x" ~: eval (Let "x" (IntExp 5) (Var "x")) Map.empty ~?= Right (IntVal 5),
      "let x = 5 in x + 1"
        ~: eval (Let "x" (IntExp 5) (Op Plus (Var "x") (IntExp 1))) Map.empty ~?= Right (IntVal 6),
      "let x = y -> y + 1 in x 3"
        ~: eval (Let "x" fun1 (App (Var "x") [IntExp 3])) Map.empty ~?= Right (IntVal 4),
      "let x = y -> y + 1 in x 3 4"
        ~: isFailing
        $ eval (Let "x" fun1 (App (Var "x") [BoolExp True, IntExp 4])) Map.empty,
      "let x = y z -> y - z in x 3 4"
        ~: eval (Let "x" fun2 (App (Var "x") [IntExp 3, IntExp 4])) Map.empty ~?= Right (IntVal (-1)),
      "let x = y z -> y - z in x True 5"
        ~: isFailing
        $ eval (Let "x" fun2 (App (Var "x") [BoolExp True, IntExp 5])) Map.empty
    ]

case1 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5), (VarP "y", Var "y")]

case2 = Case (Var "x") [(IntP 3, IntExp 3), (BoolP True, IntExp 5)]

testCasingSimple =
  TestList
    [ "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 3"
        ~: eval case1 (Map.insert "x" (IntExp 3) Map.empty) ~?= Right (IntVal 3),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = 6"
        ~: eval case1 (Map.insert "x" (IntExp 6) Map.empty) ~?= Right (IntVal 6),
      "case x of [3 -> 4, True -> 5, 'y' -> 'y'] where x = True"
        ~: eval case1 (Map.insert "x" (BoolExp True) Map.empty) ~?= Right (IntVal 5),
      "case x of [3 -> 4, True -> 5] where x = 6"
        ~: isFailing
        $ eval case2 (Map.insert "x" (IntExp 6) Map.empty)
    ]

testUserDefined =
  TestList
    [ "let x = P in x"
        ~: eval (Let "x" (C (DC "P" IntTy)) (Var "x")) Map.empty ~?= Right (UserDT (DC "P" IntTy) []),
      "let x = P 3 4 in x"
        ~: eval (Let "x" (App (C (DC "P" IntTy)) [IntExp 3, IntExp 4]) (Var "x")) Map.empty ~?= Right (UserDT (DC "P" IntTy) [IntVal 3, IntVal 4])
    ]

testFunctions :: Test
testFunctions =
  TestList
    [ "let x = a -> b -> a + b in x 4 5"
        ~: eval (Let "x" (Lam "a" (Lam "b" (Op Plus (Var "a") (Var "b")))) (App (Var "x") [IntExp 4, IntExp 5])) Map.empty ~?= Right (IntVal 9)
    ]

-- -- quickcheck property
-- -- Can be evaluated property
isValid :: Expression -> Bool
isValid = const True

-- prop_stepExec :: Expression -> Property
-- prop_stepExec e =
--   isValid e ==> not (isErr x)
--   where
--     x = evalBounded e Map.empty

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