{-# LANGUAGE AllowAmbiguousTypes #-}
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

import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map as Map
import Data.Nat
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality
import Data.Vec.Lazy (Vec)

-- TYPE LEVEL
-- ==============================
-- TC "List" (* -> *)
type TypeVariable = Char

newtype UniVariable = UV Char
  deriving (Show, Eq, Ord)

newtype InstVariable = IV Char
  deriving (Show, Eq, Ord)

-- // TODO: try doing GADT based stratification

data Type where
  IntTy :: Type
  BoolTy :: Type
  FunTy :: Type -> Type -> Type
  TyCstr :: forall k. TypeConstructor k -> Vec k Type -> Type
  TyCstrS :: String -> [Type] -> Type -- PARSING PURPOSES ONLY
  -- TyCstr :: TypeConstructor -> Vec k Type -> Type
  VarTy :: TypeVariable -> Type
  UVarTy :: UniVariable -> Type
  IVarTy :: InstVariable -> Type
  Forall :: [TypeVariable] -> Type -> Type

typesToFunTy :: NonEmpty Type -> Type
typesToFunTy (x :| []) = x
typesToFunTy (x :| (y : ys)) = FunTy x (typesToFunTy (y :| ys))

isMono :: Type -> Bool
isMono IntTy = True
isMono BoolTy = True
isMono (FunTy ty1 ty2) = isMono ty1 && isMono ty2
isMono (TyCstr _ vec) = all isMono vec
isMono (UVarTy _) = True
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

data HArity = forall k. HA (SArity k)

len :: [a] -> HArity
len [] = HA SZ
len (_ : xs) = case len xs of
  HA sa -> HA (SS sa)

-- makeHTC :: String -> HArity -> HTypeConstructor
-- makeHTC s (HA sa) = HTC (TC s sa)

-- instance Num (SArity k) where
--   a + SZ = a
--   a + (SS b) = SS (a + b)

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

-- data TypeConstructor where
--   TC :: String -> Arity -> TypeConstructor

-- deriving instance Show HTypeConstructor

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
  deriving (Show, Eq)

-- type DataConstructor = String

-- DC "Cons" [ (TC "Nat" [])]

data Pattern
  = P DataConstructor [Pattern]
  | PS String [Pattern] -- PARSING PURPOSE ONLY
  | VarP Variable
  | IntP Int
  | BoolP Bool
  deriving (Show, Eq)

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

-- data AppHead
--   = Var Variable
--   | Expr Expression
--   | Annot Expression Type
--   | C DataConstructor

-- deriving instance Show AppHead

data Expression
  = Var Variable
  | -- | user defined data constructors
    Annot Expression Type -- (x :: Int)
  | C DataConstructor
  | PC DataConstructor [Expression] -- partially constructed udt -- eval only
  | CS String -- PARSING ONLY
  | -- | primitives
    IntExp Int
  | BoolExp Bool
  | Op Bop Expression Expression
  | If Expression Expression Expression
  | Case Expression [(Pattern, Expression)]
  | Lam Variable Expression
  | App Expression [Expression] -- ((s e1) e2) e3
  | Let Variable Expression Expression
  | Mu Variable Expression
  deriving (Show, Eq)

-- var wrapper
var :: Variable -> Expression
var v = App (Var v) []

-- Annot Expression Type --

-- MISCELLANEOUS
foldableToSet :: (Ord a, Foldable f) => f a -> Set a
foldableToSet = Prelude.foldr Set.insert Set.empty
