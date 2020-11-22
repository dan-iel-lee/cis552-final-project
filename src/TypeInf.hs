module TypeInf where

type TypeVariable = Char

data Type
  = IntTy
  | Sum Type Type
  | Prod Type Type
  | Fun Type Type
  | VarTy TypeVariable
