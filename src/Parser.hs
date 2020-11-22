module Parser where

import ParserCombinators 

-- data Variable where

type Variable = String -- lowercase

type Constructor = String -- uppercase


data Pattern = 
  P Constructor [Pattern] 
  | IntP Int
  | BoolP Bool


data UserType 
  = UT { constructors :: [(Constructor, Type)] }

data Type
  = IntTy 
  | BoolTy
  | UT UserType
  | Fun Type Type
  | VarTy TypeVariable

data Kind 
  = Star | Func Star Kind


data Expression 
  = Var Variable
  -- | UserDef Constructor [Expression]
  | C Constructor
  | IntExp Int 
  | BoolExp Bool 
  | Op Bop Expression Expression
  | Case Expression [(Pattern, Expression)]
  | Fun Variable Expression
  | App Expression Expression 
  | Let Variable Expression Expression


-- L :: forall a b. a -> Either a b
a = L 3

-- fun x -> x

App (C "L") (IntExp 3)  

let a = L 3 

data Bop =
    Plus     -- +  :: Int  -> Int  -> Int
  | Minus    -- -  :: Int  -> Int  -> Int
  | Times    -- *  :: Int  -> Int  -> Int
  | Gt       -- >  :: Int -> Int -> Bool
  | Ge       -- >= :: Int -> Int -> Bool
  | Lt       -- <  :: Int -> Int -> Bool
  | Le       -- <= :: Int -> Int -> Bool
    deriving (Eq, Show, Enum)


--data T3 = A String | B Bool | C Int
-- Sum String (Sum Bool Int)
-- 

type T3' = Either String (Either Bool Int)

ex :: T3 -> Bool
ex a = case a of 
  A s -> _
  B b -> b
  C i -> _

ex' :: T3' -> Bool 
ex' a = case a of
  Left s -> s == "Karthik"
  Right x -> case x of 
    Left b -> b 
    Right i -> i > 0




> data Expression =
>  -- stuff shared with WHILE...
>    Var Variable                        -- uppercase strings 'X'
>  | IntExp  Int                         -- natural numbers   '0' ..
>  | BoolExp Bool                        -- 'true' or 'false'
>  | Op  Bop Expression Expression       -- infix binary operators 'e1 + e2'
>  -- new stuff...
>  | If Expression Expression Expression -- if expressions, 'if X then Y else Z'
>  -- interesting new stuff...
>  | Fun Variable Expression             -- anonymous function,   'fun X -> e'
>  | App Expression Expression           -- function application, 'e1 e2'
>  | Let Variable Expression Expression  -- (recursive) binding,  'let F = e in e'
>     deriving (Show, Eq)