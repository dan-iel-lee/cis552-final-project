{-# LANGUAGE RecursiveDo #-}

module Eval where

import Data.Map as Map
import Parser
import Test.HUnit
import Types

type Environment = Map Variable Value

data Value
  = IntVal Int
  | BoolVal Bool
  | -- note! function values can go wrong when they are run
    FunVal (Value -> Either String Value)

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (FunVal _) = "<function>" -- can't show functions

evalB :: Bop -> Value -> Value -> Either String Value
vLookup :: Variable -> Map Variable Value -> Either String Value
eval :: Expression -> Environment -> Either String Value
-- Testing code

isErr :: Either String Value -> Test
isErr (Left _) = TestCase $ assert True
isErr (Right _) = TestCase $ assert False

isIntVal :: Int -> Either String Value -> Test
isIntVal y (Left _) = TestCase $ assert False
isIntVal y (Right (IntVal x)) = TestCase $ assert (x == y)

-- repl

replE :: IO ()
replE = do
  putStr "%> "
  line <- getLine
  case Parser.parse line of
    Just exp ->
      case eval exp Map.empty of
        Left str -> putStrLn str >> replE
        Right val -> putStrLn (show val) >> replE
    Nothing -> putStrLn "what?!?" >> replE

-- TEST CASES

tests =
  TestList
    [ "1 + true" ~: isErr $ eval (Op Plus (IntExp 1) (BoolExp True)) Map.empty,
      "1 1" ~: isErr $ eval (App (IntExp 1) (IntExp 1)) Map.empty,
      "if 1 .." ~: isErr $ eval (If (IntExp 1) (IntExp 2) (IntExp 3)) Map.empty,
      "X" ~: isErr $ eval (Var "X") Map.empty,
      "FACT 6" ~: isIntVal 120 $ eval factExp Map.empty
    ]

-- quickcheck property
