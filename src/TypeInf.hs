{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module TypeInf where

-- import Parser

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Test.HUnit
import Types

data Constraint = Equal MonoType MonoType

data TypeEnv = TE {getExpVars :: Map Variable Scheme, getTypeVars :: [TypeVariable]}

envInsExpVar :: Variable -> Scheme -> TypeEnv -> TypeEnv
envInsExpVar x t (TE es as) = TE (Map.insert x t es) as

-- Monad where all type checking takes place
type TcMonad a =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )
    a

-- // TODO: extract out common substitution patterns
class Substible t where
  data Substy t
  after :: Substy t -> Substy t -> Substy t
  subst :: Substy t -> a -> Substy t

newtype Substitution = Subst (Map TypeVariable MonoType) deriving (Show, Eq)

newtype MonoSubst = MSubst (Map InstVariable MonoType) deriving (Show, Eq)

newtype PolySubst = PSubst (Map InstVariable Scheme) deriving (Show, Eq)

afterPoly :: PolySubst -> PolySubst -> PolySubst
PSubst s1 `afterPoly` PSubst s2 = PSubst $ Map.map (substPoly (PSubst s1)) s2 `Map.union` s1

substPolyHelper :: PolySubst -> Type -> Scheme
substPolyHelper (PSubst s) t@(IVarTy a) = fromMaybe (Rho t) (Map.lookup a s)
substPolyHelper s (RFunTy s1 s2) = Rho $ RFunTy (substPoly s s1) (substPoly s s2)
substPolyHelper _ t@(Tau _) = Rho t

substPoly :: PolySubst -> Scheme -> Scheme
substPoly s t = substPolyHelper s (strip t)

-- substitute out all instantiation variables for fresh unification (type) variables
genFreshInnerSubst :: [InstVariable] -> TcMonad MonoSubst
genFreshInnerSubst [] = return (MSubst Map.empty)
genFreshInnerSubst (x : xs) = do
  MSubst res <- genFreshInnerSubst xs
  a <- fresh
  return $ MSubst (Map.insert x (VarTy a) res)

-- HELPERS

-- | Generates a fresh type variable
fresh :: TcMonad TypeVariable
fresh = do
  s <- get
  put $ succ s
  return s

-- | Checks if two types are equal
equate :: MonoType -> MonoType -> TcMonad ()
equate = undefined

-- | Looks up a variable in a context
tLookup :: MonadError String m => Variable -> Map Variable a -> m a
tLookup x env = do
  case Map.lookup x env of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound variable " ++ x

-- | looks for the free instantiation variables of a type
fiv :: Type -> [InstVariable]
fiv (Tau _) = []
fiv (RFunTy s1 s2) = fiv (strip s1) ++ fiv (strip s2)
fiv (IVarTy v) = [v]

fivs :: [Type] -> [InstVariable]
fivs = foldMap fiv

-- | Calls inferTy to generate a type and the constraints
genConstraints :: Expression -> Either String (Type, [Constraint])
genConstraints = undefined

-- JUDGEMENTS
-- 1. check type
checkGen :: TypeEnv -> Expression -> Scheme -> TcMonad ()
checkGen (TE es as) e (Forall a s) =
  case s of
    Rho p -> checkType newEnv e p
    _ -> checkGen newEnv e s
  where
    newEnv = TE es (a : as)
checkGen env e (Rho p) = checkType env e p

checkType :: TypeEnv -> Expression -> Type -> TcMonad ()
-- LAMBDA CASES
checkType (TE es as) (Lam x e) (RFunTy s1 s2) = checkGen newEnv e s2
  where
    newEnv = TE (Map.insert x s1 es) as
checkType env (Lam x e) (Tau t@(VarTy v)) = do
  argTy <- fresh
  resTy <- fresh
  let newEnv = envInsExpVar x (sVar argTy) env
  equate t (FunTy (VarTy argTy) (VarTy resTy)) -- generate constraint
  checkType newEnv e (rVar resTy)
checkType _ e@(Lam _ _) _ = throwError $ "Invalid type for lambda at: " <> show e -- // TODO: replace with pretty print
-- APP
checkType env (App h es) rho = do
  -- infer type of head
  headTy <- inferTypeHead env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- unify with the expected type
  sub1 <- sinkScheme2 mguQL resTy rho
  -- perform substitutinos
  let argTys' = map (substPoly sub1) argTys
      resTy' = substPoly sub1 (Rho resTy)
      -- generate a substitution to get rid of instantiation vars
      stripped = map strip (resTy' : argTys')
  sub2 <- genFreshInnerSubst (fivs stripped)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys') (\(e, t) -> checkGen env e (substPoly sub2 t))
-- // TODO: all other types of types
checkType _ _ _ = error "IMPLEMENT BRO"

-- 2. infer type
inferType :: TypeEnv -> Expression -> TcMonad Type
inferType _ (IntExp _) = return $ Tau IntTy
inferType _ (BoolExp _) = return $ Tau BoolTy
inferType env (Lam x e) = do
  argTy <- fresh
  inferType (envInsExpVar x (sVar argTy) env) e
inferType env (App h es) = do
  -- infer type of head
  headTy <- inferTypeHead env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- generate a substitution to get rid of instantiation vars
  let stripped = map strip argTys ++ [resTy]
  sub <- genFreshInnerSubst (fivs stripped)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys) (\(e, t) -> checkGen env e (substPoly sub t))
  return $ substPoly sub resTy
-- // TODO: all other types of types
inferType _ _ = error "Unimplemented"

inferTypeHead :: TypeEnv -> AppHead -> TcMonad Scheme
inferTypeHead env (Var v) = tLookup v (getExpVars env)
inferTypeHead env (Annot e t) = do
  checkGen env e t
  return t
inferTypeHead env (Expr e) = Rho <$> inferType env e

-- 3. instantiate
instantiate :: TypeEnv -> Scheme -> [Expression] -> TcMonad ([Scheme], Type)
instantiate = undefined

-- 4. unification
mguQLRho :: Type -> Type -> TcMonad PolySubst
mguQLRho t1 (IVarTy v) = return $ PSubst (Map.singleton v (Rho t1))
mguQLRho (IVarTy v) t2 = return $ PSubst (Map.singleton v (Rho t2))
mguQLRho (RFunTy s1 s2) (RFunTy t1 t2) = do
  sub1 <- mguQL s1 t1
  sub2 <- mguQL (substPoly sub1 s2) (substPoly sub1 t2)
  return $ sub1 `afterPoly` sub2
mguQLRho _ _ = return $ PSubst Map.empty

mguQL :: Scheme -> Scheme -> TcMonad PolySubst
mguQL s1 s2 = mguQLRho (strip s1) (strip s2) -- // TODO: prevent variable escapture

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
      typeInference good1 ~?= Right (Tau IntTy),
      typeInference good2 ~?= Right (Tau IntTy),
      typeInference good3 ~?= Right (Tau IntTy),
      typeInference good4 ~?= Right (Tau BoolTy),
      typeInference good5 ~?= Right (Tau (FunTy IntTy IntTy)),
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
