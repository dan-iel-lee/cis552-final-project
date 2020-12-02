{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Types where

import Data.Nat
import Data.Type.Equality
import Data.Vec.Lazy

-- TYPE LEVEL
-- ==============================
-- TC "List" (* -> *)
type TypeVariable = Char

newtype InstVariable = IV Char
  deriving (Show, Eq, Ord)

-- // TODO: try doing GADT based stratification

data Type where
  IntTy :: Type
  BoolTy :: Type
  FunTy :: Type -> Type -> Type
  TyCstr :: forall k. TypeConstructor k -> Vec k Type -> Type -- strata is at least the argument stratas
  VarTy :: TypeVariable -> Type -- can be Mono or Rho
  IVarTy :: InstVariable -> Type
  Forall :: [TypeVariable] -> Type -> Type -- can be given Mono or Rho

isMono :: Type -> Bool
isMono IntTy = True
isMono BoolTy = True
isMono (FunTy ty1 ty2) = isMono ty1 && isMono ty2
isMono (TyCstr _ vec) = all isMono vec
isMono (VarTy _) = True
isMono _ = False

instance Eq Type where
  IntTy == IntTy = True
  BoolTy == BoolTy = True
  FunTy l1 r1 == FunTy l2 r2 = l1 == l2 && r1 == r2
  VarTy x == VarTy y = x == y
  IVarTy a == IVarTy b = a == b
  Forall vs1 t1 == Forall vs2 t2 = vs1 == vs2 && t1 == t2
  TyCstr tc1 vec1 == TyCstr tc2 vec2 =
    case tc1 `testEquality` tc2 of
      Just Refl -> tc1 == tc2 && vec1 == vec2
      _ -> False
  _ == _ = False

deriving instance Show Type

{- for later -}
-- data Arity
--   = Z
--   | S Arity
--   deriving (Show, Eq)
type Arity = Nat

data SArity :: Arity -> * where
  SZ :: SArity 'Z
  SS :: SArity k -> SArity (S k)

-- instance TestEquality SArity

deriving instance Show (SArity k)

deriving instance Eq (SArity k)

-- data Vec :: Arity -> * -> * where
--   Nil :: Vec Z a
--   Cons :: a -> Vec k a -> Vec (S k) a

-- deriving instance Show a => Show (Vec k a)

-- deriving instance Eq a => Eq (Vec k a)

-- // TODO: TestEquality

data TypeConstructor :: Arity -> * where
  TC :: String -> SArity k -> TypeConstructor k

-- lift term equality to type equality
instance TestEquality TypeConstructor where
  TC _ SZ `testEquality` TC _ SZ = return Refl
  TC cs (SS a1) `testEquality` TC ds (SS a2) =
    case TC cs a1 `testEquality` TC ds a2 of
      Just Refl -> return Refl
      _ -> Nothing
  _ `testEquality` _ = Nothing

(%==) :: TypeConstructor k1 -> TypeConstructor k2 -> Bool
tc1 %== tc2 =
  case tc1 `testEquality` tc2 of
    Just Refl -> tc1 == tc2
    _ -> False

deriving instance Show (TypeConstructor k)

deriving instance Eq (TypeConstructor k)

-- EXPRESSION LEVEL
-- ==============================

-- NOTE: can defer this to type checking
data DataConstructor = DC {getDCName :: String, getType :: Type} -- uppercase
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
  | Annot Expression Type
  | C DataConstructor

deriving instance Show AppHead

data Expression
  = IntExp Int
  | BoolExp Bool
  | Op Bop Expression Expression
  | -- constructors
    Case Expression [(Pattern, Expression)]
  | Lam Variable Expression
  | App AppHead [Expression] -- ((s e1) e2) e3
  | Let Variable Expression Expression
  deriving (Show)

-- var wrapper
var :: Variable -> Expression
var v = App (Var v) []

-- Annot Expression Type --