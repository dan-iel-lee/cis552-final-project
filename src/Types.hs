module Types where

-- TYPE LEVEL
-- ==============================
type TypeVariable = Char

-- TC "List" (* -> *)

data Type
  = IntTy
  | BoolTy
  | Fun Type Type
  | VarTy TypeVariable
  | -- for user defined types
    TypeC TypeConstructor [Type]
  deriving (Show, Eq)

{- for later -}
data Kind
  = Star
  | Arrow Kind
  deriving (Show, Eq)

-- List (Arrow Star) Star -> Star (* -> *) -> *

data TypeConstructor = TC {getTCName :: String, getKind :: Kind}
  deriving (Show, Eq)

-- EXPRESSION LEVEL
-- ==============================

-- NOTE: can defer this to type checking
data DataConstructor = DC {getDCName :: String, getType :: [Type]} -- uppercase
  deriving (Show, Eq)

-- type DataConstructor = String

-- DC "Cons" [ (TC "Nat" [])]

data Pattern
  = P DataConstructor [Pattern]
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

data AppHead
  = Var Variable
  | Expr Expression
  | Annot Expression Type
  deriving (Show, Eq)

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
  deriving (Show, Eq)

-- Annot Expression Type --