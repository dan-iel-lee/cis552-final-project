module TypeInf where

import Parser

data Constraint = Equal Type Type

-- Monad where all type checking takes place
type TcMonad a =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )
    a

-- HELPERS

-- | Generates a fresh type variable
fresh :: TcMonad TypeVariable

-- | Checks if two types are equal
equate :: Type -> Type -> TcMonad ()

-- | infers a type based on an expression
inferTy :: Expression -> TypeEnv -> TcMonad Type

-- | Calls inferTy to generate a type and the constraints
genConstraints :: Expression -> Either String (Type, [Constraint])
--
--
-- Putting stuff together
solve :: [Constraint] -> Either String Substitution
-- Infers the type of an expression
typeInference :: Expression -> Either String Type

-- | Used by Eval to filter ill-typed expressions
isValid :: Expression -> Bool

-- TESTING
-- bunch of test cases

{-
x = 5
y = 6

() -- Unit

let x = 5 in ()

x :: x
alpha ~ Int

solve => [alpha := Int]

-}
