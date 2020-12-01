module Types where

-- TYPE LEVEL
-- ==============================
-- TC "List" (* -> *)
type TypeVariable = Char

newtype InstVariable = IV Char
  deriving (Show, Eq, Ord)

-- monotypes
data MonoType
  = IntTy -- i.e. 'Int'
  | BoolTy -- i.e. 'Bool'
  | FunTy MonoType MonoType -- i.e. t1 -> t2
  | VarTy TypeVariable -- we'll get to this later
  deriving (Eq, Show)

-- top level mono (rho type)
data Type
  = IVarTy InstVariable -- instantiation variable
  | RFunTy Scheme Scheme
  | Tau MonoType
  deriving (Show, Eq)

-- top level poly
data Scheme
  = Forall [TypeVariable] Type
  deriving (Show, Eq)

-- wrap rho type in scheme
rho :: Type -> Scheme
rho = Forall []

--  | Rho Type

-- monotype to rho type
-- mToR :: MonoType -> Type
-- mToR

liftMtoR :: (MonoType -> MonoType) -> Type -> Type
liftMtoR f (Tau mt) = Tau (f mt)
liftMtoR f (RFunTy s1 s2) = RFunTy (liftMtoS f s1) (liftMtoS f s2)
liftMtoR _ t@(IVarTy _) = t

-- lift a Type function to a Scheme function
liftRtoS :: (Type -> Type) -> Scheme -> Scheme
liftRtoS f (Forall vs t) = Forall vs (f t)

-- liftRtoS f (Rho t) = Rho $ f t

liftMtoS :: (MonoType -> MonoType) -> Scheme -> Scheme
liftMtoS = liftRtoS . liftMtoR

-- "sink" a function which takes Schemes to a function which takes Types
sinkScheme :: (Scheme -> a) -> Type -> a
sinkScheme f t = f (rho t)

sinkScheme2 :: (Scheme -> Scheme -> a) -> Type -> Type -> a
sinkScheme2 f t1 t2 = f (rho t1) (rho t2)

{- for later -}
data Kind
  = Star
  | Arrow Kind
  deriving (Show, Eq)

-- HELPER FUNCS

-- create a unification variable, wrapped in a Rho Type
rVar :: TypeVariable -> Type
rVar = Tau . VarTy

-- create a unification variable, wrapped in a Scheme
sVar :: TypeVariable -> Scheme
sVar = rho . rVar

-- strip a Scheme
strip :: Scheme -> Type
strip (Forall _ t) = t

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
  | Annot Expression Scheme
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