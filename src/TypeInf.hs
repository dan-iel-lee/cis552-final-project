module TypeInf where

-- import Parser

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import Data.Set (Set)
import Test.HUnit
import Types

data Constraint = Equal Type Type

type TypeEnv = Map Variable Scheme

data Scheme = Forall (Set TypeVariable) Type

-- Monad where all type checking takes place
type TcMonad a =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )
    a

newtype Substitution = Subst (Map TypeVariable Type) deriving (Show, Eq)

-- HELPERS

-- | Generates a fresh type variable
fresh :: TcMonad TypeVariable
fresh = undefined

-- | Checks if two types are equal
equate :: Type -> Type -> TcMonad ()
equate = undefined

-- | infers a type based on an expression
inferTy :: Expression -> TypeEnv -> TcMonad Type
inferTy = undefined

-- | Calls inferTy to generate a type and the constraints
genConstraints :: Expression -> Either String (Type, [Constraint])
genConstraints = undefined

--
--
-- Putting stuff together
solve :: [Constraint] -> Either String Substitution
solve = undefined

-- Infers the type of an expression
typeInference :: Expression -> Either String Type
typeInference = undefined

-- | Used by Eval to filter ill-typed expressions
isValid :: Expression -> Bool
isValid = undefined

-- TESTING
-- bunch of test cases

-- GOOD CASES
-- let f = \x -> x in (f 1)

var :: Variable -> Expression
var v = App (Var v) []

good1 = Let "f" (Lam "x" (var "x")) (App (Var "f") [IntExp 1])

-- test constraint solving:
-- let f = \x -> x + 1 in (f 1)
good2 = Let "f" (Lam "x" (Op Plus (var "x") (IntExp 1))) (App (Var "f") [IntExp 1])

-- test Spine based application
-- (\x,y -> x + y) 1 2
good3 = App (Expr $ Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1, IntExp 2]

-- test polymorphism
-- let f = \x -> x in let a = f True in f 1
good4 = Let "f" (Lam "x" (App (Var "x") [])) (Let "a" (App (Var "f") [IntExp 1]) (App (Var "f") [BoolExp True]))

-- partial application
-- (\x, y -> x + y) 1
good5 = App (Expr $ Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1]

-- BAD CASES
-- bad operator parameters
bad1 = Op Plus (IntExp 1) (BoolExp True)

-- wrong shape
bad2 = App (Expr $ Lam "x" (Op Plus (var "x") (IntExp 1))) [IntExp 1, IntExp 2]

testTypeInf =
  TestList
    [ -- good
      typeInference good1 ~?= Right IntTy,
      typeInference good2 ~?= Right IntTy,
      typeInference good3 ~?= Right IntTy,
      typeInference good4 ~?= Right BoolTy,
      typeInference good5 ~?= Right (FunTy IntTy IntTy),
      -- bad
      typeInference bad1 ~?= Left "bad operator parameters",
      typeInference bad2 ~?= Left "function applied to too many arguments"
    ]

{-
x = 5
y = 6

() -- Unit

let x = 5 in ()

x :: x
alpha ~ Int

solve => [alpha := Int]

-}
