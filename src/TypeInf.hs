{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
import Data.Nat
import Data.Type.Equality
import Data.Vec.Lazy (Vec (VNil, (:::)), zipWith)
import Test.HUnit
import Types
import Prelude hiding (zipWith)

data Constraint = Equal Type Type
  deriving (Show, Eq)

data TypeEnv = TE {getExpVars :: Map Variable Type, getTypeVars :: [TypeVariable]}
  deriving (Show, Eq)

emptyEnv :: TypeEnv
emptyEnv = TE Map.empty []

envInsExpVar :: Variable -> Type -> TypeEnv -> TypeEnv
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

{-
Types of substitution
- instantiation variables for SIgma types

 -}

class Subst a where
  data Substitution a
  empty :: Substitution a
  subst :: Substitution a -> Type -> Type
  after :: Substitution a -> Substitution a -> Substitution a

-- subst ::

instance Subst InstVariable where
  data Substitution InstVariable = SI (Map InstVariable Type) deriving (Show, Eq)
  empty = SI Map.empty

  subst (SI m) t@(IVarTy a) = fromMaybe t (Map.lookup a m)
  subst m (FunTy s1 s2) = FunTy (subst m s1) (subst m s2)
  subst s (Forall vs t) =
    let resTy = subst s t
     in Forall vs resTy
  subst s (TyCstr tc vec) = TyCstr tc $ fmap (subst s) vec
  subst _ t = t

  s1@(SI m1) `after` (SI m2) = SI $ Map.map (subst s1) m2 `Map.union` m1

instance Subst TypeVariable where
  data Substitution TypeVariable = SU (Map TypeVariable Type) deriving (Show, Eq)
  empty = SU Map.empty

  subst (SU m) t@(VarTy a) = fromMaybe t (Map.lookup a m)
  subst m (FunTy s1 s2) = FunTy (subst m s1) (subst m s2)
  subst s (Forall vs t) =
    let resTy = subst s t
     in Forall vs resTy
  subst s (TyCstr tc vec) = TyCstr tc (fmap (subst s) vec)
  subst _ t = t

  s1@(SU m1) `after` (SU m2) = SU $ Map.map (subst s1) m2 `Map.union` m1

-- substitute out all instantiation variables for fresh unification (type) variables
genFreshInnerSubst :: [InstVariable] -> TcMonad (Substitution InstVariable)
genFreshInnerSubst [] = return empty
genFreshInnerSubst (x : xs) = do
  SI res <- genFreshInnerSubst xs
  a <- fresh
  return $ SI (Map.insert x (VarTy a) res)

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
equate :: Type -> Type -> TcMonad ()
equate t1 t2
  | t1 == t2 = return ()
  | otherwise = tell [Equal t1 t2]

-- | Looks up a variable in a context
tLookup :: MonadError String m => Variable -> Map Variable a -> m a
tLookup x env = do
  case Map.lookup x env of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound variable " ++ x

-- | looks for the free instantiation variables of a type
fiv :: Type -> [InstVariable]
fiv (FunTy ty1 ty2) = fiv ty1 ++ fiv ty2
fiv (IVarTy v) = [v]
fiv (Forall _ ty) = fiv ty
-- go through all arguments and check for free instantiation variables
fiv (TyCstr _ args) = foldr (\x acc -> fiv x ++ acc) [] args
fiv _ = []

-- // TODO: other cases for fiv
-- fiv (TyCstr _ )

fivs :: [Type] -> [InstVariable]
fivs = foldMap fiv

-- | Calls inferTy to generate a type and the constraints
genConstraints :: Expression -> Either String (Type, [Constraint])
genConstraints = undefined

-- JUDGEMENTS
-- 1. check type

checkType :: TypeEnv -> Expression -> Type -> TcMonad ()
-- GEN
checkType (TE es as) e (Forall vs t) = checkType newEnv e t
  where
    newEnv = TE es (as ++ vs)
-- LAMBDA CASES
checkType (TE es as) (Lam x e) (FunTy s1 s2) = checkType newEnv e s2
  where
    newEnv = TE (Map.insert x s1 es) as
checkType env (Lam x e) t@(VarTy v) = do
  argTy <- fresh
  resTy <- fresh
  let newEnv = envInsExpVar x (VarTy argTy) env
  equate t (FunTy (VarTy argTy) (VarTy resTy)) -- generate constraint
  checkType newEnv e (VarTy resTy)
checkType _ e@(Lam _ _) _ = throwError $ "Invalid type for lambda at: " <> show e -- // TODO: replace with pretty print
-- APP
checkType env (App h es) rho = do
  -- infer type of head
  headTy <- inferTypeHead env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- unify with the expected type
  sub1 <- mguQL resTy rho
  -- perform substitutinos
  let argTys' = map (subst sub1) argTys
      resTy' = subst sub1 resTy
      -- generate a substitution to get rid of instantiation vars
      together = resTy' : argTys'
  sub2 <- genFreshInnerSubst (fivs together)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys') (\(e, t) -> checkType env e (subst sub2 t))
checkType _ (IntExp _) ty
  | isMono ty = equate ty IntTy
checkType _ (BoolExp _) ty
  | isMono ty = equate ty BoolTy
-- // TODO: all other types of types
checkType env e ty = throwError $ "Fail checkType: " <> show env <> " " <> show e <> " " <> show ty

-- checkType _ _ _ = error "IMPLEMENT BRO"

-- 2. infer type
inferType :: TypeEnv -> Expression -> TcMonad Type
inferType _ (IntExp _) = return IntTy
inferType _ (BoolExp _) = return BoolTy
inferType env (Lam x e) = do
  argTy <- fresh
  inferType (envInsExpVar x (VarTy argTy) env) e
inferType env (App h es) = do
  -- infer type of head
  headTy <- inferTypeHead env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- generate a substitution to get rid of instantiation vars
  let together = resTy : argTys
  sub <- genFreshInnerSubst (fivs together)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys) (\(e, t) -> checkType env e (subst sub t))
  return $ subst sub resTy
-- // TODO: all other types of types
inferType _ _ = error "Unimplemented"

inferTypeHead :: TypeEnv -> AppHead -> TcMonad Type
inferTypeHead env (Var v) = tLookup v (getExpVars env)
inferTypeHead env (Annot e t) = do
  checkType env e t
  return t
inferTypeHead env (Expr e) = inferType env e
inferTypeHead _ (C (DC _ ty)) = return ty -- // TODO: check if ty is actually a type

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

instantiate :: TypeEnv -> Type -> [Expression] -> TcMonad ([Type], Type)
instantiate env sTy es = do
  (_, sTys, ty) <- evalStateT (instantiateAux env sTy es) (IV 'K')
  return (sTys, ty)

instantiateAux :: TypeEnv -> Type -> [Expression] -> InstMonad (Substitution InstVariable, [Type], Type)
-- IALL - generate instantiation variable
instantiateAux env (Forall (v : vs) ty) es = do
  -- generate fresh variables and substitution
  iv <- freshIV
  let sub = SU (Map.singleton v (IVarTy iv))
  instantiateAux env (subst sub (Forall vs ty)) es
instantiateAux env (Forall [] ty) es = instantiateAux env ty es
-- IARG - take a quick look at the argument
instantiateAux env (FunTy st1 st2) (e : es) = do
  -- take a quick look at the argument to generate a substitution
  sub1 <- qlArgument env e st1
  -- then do instantiation on the rest
  (sub2, argTys, resTy) <- instantiateAux env (subst sub1 st2) es
  -- combine the substitutions
  let sub = sub2 `after` sub1
  -- substitute in the first argument
  return (sub, subst sub st1 : argTys, resTy)
-- unification variable case
instantiateAux env (VarTy v) (e : es) = do
  -- generate fresh variables for argument and return types
  argTV <- lift fresh
  resTV <- lift fresh
  -- v ~ argTV -> resTV
  let newType = FunTy (VarTy argTV) (VarTy resTV)
  lift $ equate (VarTy v) newType
  -- check with new type
  instantiateAux env newType (e : es)
-- instantiation variable case
instantiateAux env (IVarTy v) (e : es) = do
  -- generate fresh instantiation vars
  argTV <- freshIV
  resTV <- freshIV
  -- argTV -> resTV
  let newType = FunTy (IVarTy argTV) (IVarTy resTV)
      sub1 = SI (Map.singleton v newType)
  -- check with new type
  (sub2, argTys, resTy) <- instantiateAux env newType (e : es)
  -- combine the substitutions
  return (sub2 `after` sub1, argTys, resTy)
instantiateAux _ ty [] = return (empty, [], ty)
instantiateAux env ty es = throwError $ "Fail: " <> show env <> "  " <> show ty <> "  " <> show es

-- QUICK LOOK JUDGEMENTS // TODO: add other cases
qlArgument :: TypeEnv -> Expression -> Type -> InstMonad (Substitution InstVariable)
qlArgument env (App h es) pTy = do
  -- infer type of head
  sTy <- qlHead env h
  (_, retTy) <- lift $ instantiate env sTy es
  if isGuarded pTy || noFIVs retTy
    then lift $ mguQL pTy retTy
    else return empty
-- qlArgument env IntTy
qlArgument _ _ _ = return empty

qlHead :: TypeEnv -> AppHead -> InstMonad Type
qlHead env (Var v) = tLookup v (getExpVars env)
qlHead _ (Annot _ sTy) = return sTy
qlHead _ (C (DC _ ty)) = return ty
qlHead _ _ = throwError "Failure: ql head doesn't allow arbitrary expressions (?)"

-- check if a type is guarded, for quick look purposes
isGuarded :: Type -> Bool
isGuarded (FunTy _ _) = True
isGuarded TyCstr {} = True
isGuarded _ = False

noFIVs :: Type -> Bool
noFIVs t = null (fiv t)

-- return undefined

-- 4. unification
mguQL :: Type -> Type -> TcMonad (Substitution InstVariable)
mguQL t1 (IVarTy v) = return $ SI (Map.singleton v t1)
mguQL (IVarTy v) t2 = return $ SI (Map.singleton v t2)
mguQL (FunTy s1 s2) (FunTy t1 t2) = do
  sub1 <- mguQL s1 t1
  sub2 <- mguQL (subst sub1 s2) (subst sub1 t2)
  return $ sub1 `after` sub2
mguQL (TyCstr tc1 vec1) (TyCstr tc2 vec2) =
  case tc1 `testEquality` tc2 of
    Just Refl ->
      if tc1 == tc2
        then
          foldM
            ( \acc (ty1, ty2) -> do
                sub <- mguQL (subst acc ty1) (subst acc ty2)
                return $ acc `after` sub
            )
            empty
            (zipWith ((,)) vec1 vec2)
        else throwError $ "Incompatible type constructors " <> show tc1 <> " and " <> show tc2
    _ -> throwError $ "Incompatible type constructors " <> show tc1 <> " and " <> show tc2
mguQL _ _ = return empty

-- mguQL :: Type -> Type -> TcMonad (Substy InstVariable Scheme)
-- mguQL s1 s2 = mguQLRho (strip s1) (strip s2) -- // TODO: prevent variable escapture

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
      typeInference good1 ~?= Right IntTy,
      typeInference good2 ~?= Right IntTy,
      typeInference good3 ~?= Right IntTy,
      typeInference good4 ~?= Right BoolTy,
      typeInference good5 ~?= Right (FunTy IntTy IntTy),
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

-- EXAMPLES AND FUN
listTC :: TypeConstructor (S Z)
listTC = TC "List" (SS SZ)

listTy :: TypeVariable -> Type
listTy v = TyCstr listTC (VarTy v ::: VNil)

consTy :: Type
consTy = Forall ['a'] (FunTy (VarTy 'a') (FunTy (listTy 'a') (listTy 'a')))

nilTy :: Type
nilTy = Forall ['a'] (TyCstr listTC (VarTy 'a' ::: VNil))

consExp :: AppHead
consExp = C (DC "cons" consTy)

nilExp :: Expression
nilExp = App (C (DC "nil" nilTy)) []

ex1 :: Expression
ex1 = App consExp [IntExp 1, nilExp]

-- polymorphism example (id : ids) -- WORKS!
idTy :: Type
idTy = Forall ['b'] (FunTy (VarTy 'b') (VarTy 'b'))

idsTy :: Type
idsTy = TyCstr listTC (idTy ::: VNil)

idsCtx :: TypeEnv
idsCtx = TE (Map.fromList [("id", idTy), ("ids", idsTy)]) []

ex2 :: Expression
ex2 = App consExp [var "id", var "ids"]

runTc :: TcMonad a -> Either String (a, [Constraint])
runTc m = evalStateT (runWriterT m) 'a'