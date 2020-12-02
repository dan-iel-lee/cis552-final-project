{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module TypeInf where

{-

Done
- type checking/inference for Vars, lambdas, and applications
- mgu for quick look
- figure out substitutions

Next up
- instantiation judgement

-}
-- import Parser

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set, fromList)
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
class Substible v t where
  data Substy v t :: *

  after :: Substy v t -> Substy v t -> Substy v t
  empty :: Substy v t
  s1 `after` s2 = smap s1 s2 `union` s1
  smap :: Substy v t -> Substy v t -> Substy v t
  union :: Substy v t -> Substy v t -> Substy v t
  subst :: Substy v t -> Type -> t
  substS :: Substy v t -> Scheme -> Scheme

instance Substible InstVariable Scheme where
  data Substy InstVariable Scheme = SSubst (Map InstVariable Scheme) deriving (Show, Eq)
  empty = SSubst Map.empty
  smap s (SSubst s1) = SSubst $ Map.map (substS s) s1
  union (SSubst s1) (SSubst s2) = SSubst (s1 `Map.union` s2)

  subst (SSubst s) t@(IVarTy a) = fromMaybe (rho t) (Map.lookup a s)
  subst s (RFunTy s1 s2) = rho $ RFunTy (substS s s1) (substS s s2)
  subst _ t@(Tau _) = rho t

  substS s (Forall vs t) =
    let Forall ys resTy = subst s t
     in Forall (vs ++ ys) resTy

-- substS

instance Substible InstVariable Type where
  data Substy InstVariable Type = PSubst (Map InstVariable Type) deriving (Show, Eq)
  empty = PSubst Map.empty
  smap s (PSubst s1) = PSubst $ Map.map (subst s) s1
  union (PSubst s1) (PSubst s2) = PSubst (s1 `Map.union` s2)

  subst (PSubst s) t@(IVarTy a) = fromMaybe t (Map.lookup a s)
  subst s (RFunTy s1 s2) = RFunTy (substS s s1) (substS s s2)
  subst _ t@(Tau _) = t

  substS s (Forall vs t) =
    let resTy = subst s t
     in Forall vs resTy

instance Substible TypeVariable Type where
  data Substy TypeVariable Type = Subst (Map TypeVariable Type) deriving (Show, Eq)
  empty = Subst Map.empty
  smap s (Subst s1) = Subst $ Map.map (subst s) s1
  union (Subst s1) (Subst s2) = Subst (s1 `Map.union` s2)

  subst _ t@(IVarTy _) = t
  subst s (RFunTy s1 s2) = RFunTy (substS s s1) (substS s s2)
  subst (Subst m) t@(Tau mTy) = substM mTy
    where
      substM (VarTy v) = fromMaybe t (Map.lookup v m)
      substM (FunTy t1 t2) = RFunTy (rho $ substM t1) (rho $ substM t2)
      substM t = Tau t

  substS s (Forall vs t) =
    let resTy = subst s t
     in Forall vs resTy

-- newtype Substitution = Subst (Map TypeVariable MonoType) deriving (Show, Eq)

-- afterPoly :: PolySubst -> PolySubst -> PolySubst
-- SSubst s1 `afterPoly` SSubst s2 = SSubst $ Map.map (subst (SSubst s1)) s2 `Map.union` s1

-- substHelper :: Substy Scheme -> Type -> Scheme
-- substHelper (SSubst s) t@(IVarTy a) = fromMaybe (Rho t) (Map.lookup a s)
-- substHelper s (RFunTy s1 s2) = Rho $ RFunTy (subst s s1) (subst s s2)
-- substHelper _ t@(Tau _) = Rho t

-- substitute out all instantiation variables for fresh unification (type) variables
genFreshInnerSubst :: [InstVariable] -> TcMonad (Substy InstVariable Type)
genFreshInnerSubst [] = return empty
genFreshInnerSubst (x : xs) = do
  PSubst res <- genFreshInnerSubst xs
  a <- fresh
  return $ PSubst (Map.insert x (Tau $ VarTy a) res)

-- HELPERS

-- | Generates a fresh type variable
fresh :: TcMonad TypeVariable
fresh = do
  s <- get
  put $ succ s
  return s

freshIV :: InstMonad InstVariable
freshIV = do
  -- // TODO: combine with fresh
  (IV s) <- get
  put $ IV (succ s)
  return (IV s)

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
checkGen (TE es as) e (Forall vs t) = checkType newEnv e t
  where
    newEnv = TE es (as ++ vs)

-- checkGen env e (rho p) = checkType env e p

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
  let argTys' = map (substS sub1) argTys
      resTy' = subst sub1 resTy
      -- generate a substitution to get rid of instantiation vars
      stripped = map strip (resTy' : argTys')
  sub2 <- genFreshInnerSubst (fivs stripped)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys') (\(e, t) -> checkGen env e (liftRtoS (subst sub2) t))
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
  forM_ (zip es argTys) (\(e, t) -> checkGen env e (liftRtoS (subst sub) t))
  return $ subst sub resTy
-- // TODO: all other types of types
inferType _ _ = error "Unimplemented"

inferTypeHead :: TypeEnv -> AppHead -> TcMonad Scheme
inferTypeHead env (Var v) = tLookup v (getExpVars env)
inferTypeHead env (Annot e t) = do
  checkGen env e t
  return t
inferTypeHead env (Expr e) = rho <$> inferType env e

-- 3. instantiate
-- need to keep track of instantiation vars
-- a partially applied TcMonad
type TcMonad' =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )

type InstMonad a = StateT InstVariable TcMonad' a

instantiate :: TypeEnv -> Scheme -> [Expression] -> TcMonad ([Scheme], Type)
instantiate env sTy es = do
  (_, sTys, ty) <- evalStateT (instantiateAux env sTy es) (IV 'K')
  return (sTys, ty)

instantiateAux :: TypeEnv -> Scheme -> [Expression] -> InstMonad (Substy InstVariable Scheme, [Scheme], Type)
-- IALL - generate instantiation variable
instantiateAux env (Forall (v : vs) ty) es = do
  iv <- freshIV
  let sub = Subst (Map.singleton v (IVarTy iv))
  instantiateAux env (substS sub (Forall vs ty)) es
-- IARG - take a quick look at the argument
instantiateAux env (Forall [] ty) (e : es) = case ty of
  RFunTy st1 st2 -> do
    -- take a quick look at the argument to generate a substitution
    sub1 <- qlArgument env e st1
    -- then do instantiation on the rest
    (sub2, argTys, resTy) <- instantiateAux env (substS sub1 st2) es
    -- combine the substitutions
    let sub = sub2 `after` sub
    -- substitute in the first argument
    return (sub, substS sub st1 : argTys, resTy)
  -- unification variable case
  (Tau (VarTy v)) -> do
    -- generate fresh variables for argument and return types
    argTV <- lift fresh
    resTV <- lift fresh
    -- v ~ argTV -> resTV
    let newType = FunTy (VarTy argTV) (VarTy resTV)
    lift $ equate (VarTy v) newType
    -- check with new type
    instantiateAux env (tau newType) (e : es)
  -- instantiation variable case
  (IVarTy v) -> do
    -- generate fresh instantiation vars
    argTV <- freshIV
    resTV <- freshIV
    -- argTV -> resTV
    let newType = rho $ RFunTy (rho $ IVarTy argTV) (rho $ IVarTy resTV)
        sub1 = SSubst (Map.singleton v newType)
    -- check with new type
    (sub2, argTys, resTy) <- instantiateAux env newType (e : es)
    -- combine the substitutions
    return (sub2 `after` sub1, argTys, resTy)
  _ -> throwError "Instantiation failed"
instantiateAux _ (Forall [] ty) [] = return (empty, [], ty)

-- QUICK LOOK JUDGEMENTS
qlArgument :: TypeEnv -> Expression -> Scheme -> InstMonad (Substy InstVariable Scheme)
qlArgument env (App h es) (Forall [] pTy) = do
  -- infer type of head
  sTy <- qlHead env h
  (_, retTy) <- lift $ instantiate env sTy es
  if isGuarded pTy || noFIVs retTy
    then lift $ mguQLRho pTy retTy
    else return empty
qlArgument _ _ _ = return empty

qlHead :: TypeEnv -> AppHead -> InstMonad Scheme
qlHead env (Var v) = tLookup v (getExpVars env)
qlHead _ (Annot _ sTy) = return sTy
qlHead _ _ = throwError "Failure: ql head doesn't allow arbitrary expressions (?)"

-- check if a type is guarded, for quick look purposes
isGuarded :: Type -> Bool
isGuarded (RFunTy _ _) = True
isGuarded (Tau (FunTy _ _)) = True
isGuarded _ = False

noFIVs :: Type -> Bool
noFIVs t = null (fiv t)

-- return undefined

-- 4. unification
mguQLRho :: Type -> Type -> TcMonad (Substy InstVariable Scheme)
mguQLRho t1 (IVarTy v) = return $ SSubst (Map.singleton v (rho t1))
mguQLRho (IVarTy v) t2 = return $ SSubst (Map.singleton v (rho t2))
mguQLRho (RFunTy s1 s2) (RFunTy t1 t2) = do
  sub1 <- mguQL s1 t1
  sub2 <- mguQL (substS sub1 s2) (substS sub1 t2)
  return $ sub1 `after` sub2
mguQLRho _ _ = return empty

mguQL :: Scheme -> Scheme -> TcMonad (Substy InstVariable Scheme)
mguQL s1 s2 = mguQLRho (strip s1) (strip s2) -- // TODO: prevent variable escapture

--
--
-- Putting stuff together
-- solve :: [Constraint] -> Either String Substitution
-- solve = undefined

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
