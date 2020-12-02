{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Types where

import Data.Type.Equality

-- TYPE LEVEL
-- ==============================
-- TC "List" (* -> *)
type TypeVariable = Char

newtype InstVariable = IV Char
  deriving (Show, Eq, Ord)

-- // TODO: try doing GADT based stratification
data Strat
  = Mono
  | Rho
  | Sigma
  deriving (Show, Eq)

instance Ord Strat where -- Mono <= Rho <= Sigma
  Mono <= _ = True
  _ <= Sigma = True
  Rho <= Rho = True
  _ <= _ = False

-- constraint enforcing type stratification
class (<==) (a :: Strat) (b :: Strat)

instance Mono <== Mono

instance Mono <== Rho

instance Mono <== Sigma

instance Rho <== Rho

instance Rho <== Sigma

instance Sigma <== Sigma

data Type :: Strat -> * where
  IntTy :: Type f
  BoolTy :: Type f
  FunTy :: (f1 <== f', f2 <== f') => Type f1 -> Type f2 -> Type f' -- strata is the max of the two stratas
  TyCstr :: (f <== f') => TypeConstructor k -> Vec k (Type f) -> Type f' -- strata is at least the argument stratas
  VarTy :: TypeVariable -> Type f -- can be Mono or Rho
  IVarTy :: (Rho <== f) => InstVariable -> Type f
  Forall :: (f <== Rho) => [TypeVariable] -> Type f -> Type Sigma -- can be given Mono or Rho

-- deriving instance Eq (Type f)

deriving instance Show (Type f)

data OldType = forall f. OT (Type f)

deriving instance Show OldType

{- for later -}
data Arity
  = Z
  | S Arity
  deriving (Show, Eq)

data SArity :: Arity -> * where
  SZ :: SArity 'Z
  SS :: SArity k -> SArity (S k)

-- instance TestEquality SArity

deriving instance Show (SArity k)

deriving instance Eq (SArity k)

data Vec :: Arity -> * -> * where
  Nil :: Vec Z a
  Cons :: a -> Vec k a -> Vec (S k) a

deriving instance Show a => Show (Vec k a)

deriving instance Eq a => Eq (Vec k a)

-- // TODO: TestEquality

data TypeConstructor :: Arity -> * where
  TC :: String -> SArity k -> TypeConstructor k

deriving instance Show (TypeConstructor k)

deriving instance Eq (TypeConstructor k)

-- EXPRESSION LEVEL
-- ==============================

-- NOTE: can defer this to type checking
data DataConstructor = DC {getDCName :: String, getType :: [OldType]} -- uppercase
  deriving (Show)

-- type DataConstructor = String

-- DC "Cons" [ (TC "Nat" [])]

data Pattern
  = P DataConstructor [Pattern]
  | VarP Variable
  | IntP Int
  | BoolP Bool
  deriving (Show)

-- primitive binary operators (for now)
data Bop
  = Plus -- +  :: Int  -> Int  -> Int
  | Minus -- -  :: Int  -> Int  -> Int
  | Times --  *  :: Int  -> Int  -> Int
  | Gt -- >  :: Int -> Int -> Bool
  | Ge -- >= :: Int -> Int -> Bool
  | Lt -- <  :: Int -> Int -> Bool
  | Le -- <= :: Int -> Int -> Bool
  deriving (Eq, Show, Enum)

type Variable = String -- lowercase

data AppHead
  = Var Variable
  | Expr Expression
  | Annot Expression OldType

deriving instance Show AppHead

data Expression
  = IntExp Int
  | BoolExp Bool
  | Op Bop Expression Expression
  | -- constructors
    Case Expression [(Pattern, Expression)]
  | C DataConstructor
  | Lam Variable Expression
  | App AppHead [Expression] -- ((s e1) e2) e3
  | Let Variable Expression Expression
  deriving (Show)

-- Annot Expression Type --