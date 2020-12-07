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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality
import Data.Vec.Lazy (Vec (VNil, (:::)), zipWith)
import Parser
import Test.HUnit
import Types
import Prelude hiding (zipWith)

{-
==================================================================
                  Types and Other Intro Stuff
==================================================================

We start off by the data types we'll be using through the rest of
this module.
-}

-- | The typing context
data TypeEnv = TE
  { -- | Bound variables and their types (ex. x : IntTy)
    getExpVars :: Map Variable Type,
    -- | Type variables in context
    getTypeVars :: Set TypeVariable
  }
  deriving (Show, Eq)

emptyEnv :: TypeEnv
emptyEnv = TE Map.empty Set.empty

instance Monoid TypeEnv where
  mempty = emptyEnv

instance Semigroup TypeEnv where
  (TE es1 ts1) <> (TE es2 ts2) = TE (es1 <> es2) (ts1 <> ts2)

-- | env |: (v, ty)
-- | adds the variable and type to the context of bound variables
(|:) :: TypeEnv -> (Variable, Type) -> TypeEnv
(TE es as) |: (x, t) = TE (Map.insert x t es) as

-- | Equality constraints generated during type inference
-- and solved afterwards via unification
data Constraint = Equal Type Type
  deriving (Show, Eq)

-- | Generates an equality constraint
-- equate :: Type -> Type -> TcMonad ()
equate :: MonadWriter [Constraint] m => Type -> Type -> m ()
equate t1 t2
  | t1 == t2 = return ()
  | otherwise = tell [Equal t1 t2]

type TcMonad' =
  WriterT
    -- gathered constraints
    [Constraint]
    ( StateT
        -- generator for new type variables
        TypeVariable
        -- error messages (for unbound variables)
        (Either String)
    )

-- | Monad where all type checking takes place
type TcMonad a = TcMonad' a

-- | Monad where type instantiation takes place
-- wraps TcMonad
type InstMonad a = StateT InstVariable TcMonad' a

{-
==================================================================
                        Substitutions
==================================================================

In this section, we define a 'Subst' type class parametrized by
the type of thing being substituted for. In our case, we
have two instances: for InstVariable and TypeVariable.

InstVariables are used purely in the 'instantiate' judgement and
can be instantiated for polytypes.

TypeVariables are used in the final constraint based unification
step and can be instantiated only with monotypes.

We also define a useful helper method 'substInstForUni' which
takes a list of Instantiation variables and creates a substitution
replacing those instantiation variables with (fresh) unification
vars.
-}
type Substitution a = Map a Type

class (Ord a, Show a) => Subst a where
  singSubst :: a -> Type -> Substitution a
  singSubst = Map.singleton

  emptySubst :: Substitution a
  emptySubst = Map.empty

  wrap :: Char -> a

  -- | perform the given substitution on a type to yield another type
  subst :: Substitution a -> Type -> Type

  -- | perform one substitution and then the other
  after :: Substitution a -> Substitution a -> Substitution a

  -- | a way to find free variables in a type
  freeV :: Type -> Set a

  -- | Create substitutino assigning variable to a type
  varAsgn :: MonadError [Char] m => Char -> Type -> m (Substitution a)
  varAsgn a t
    | t == VarTy a = return emptySubst
    | t == IVarTy (IV a) = return emptySubst
    | a `Set.member` freeV t =
      throwError $
        "occur check fails: " ++ show a ++ " in " ++ show t
    | otherwise = return $ singSubst (wrap a) t

-- | Helper function to perform a substitution on a typing environment
substEnv :: Subst a => Substitution a -> TypeEnv -> TypeEnv
substEnv s (TE env as) = TE (Map.map (subst s) env) as

-- subst ::

-- // TODO: try to combien the two subst definitions cause they're so similar
instance Subst InstVariable where
  -- data Substitution InstVariable = SI (Map InstVariable Type) deriving (Show, Eq)
  wrap = IV

  subst m t@(IVarTy a) = fromMaybe t (Map.lookup a m)
  subst m (FunTy s1 s2) = FunTy (subst m s1) (subst m s2)
  subst s (Forall vs t) =
    let resTy = subst s t
     in Forall vs resTy
  subst s (TyCstr tc vec) = TyCstr tc $ fmap (subst s) vec
  subst _ t = t

  freeV = fiv

  -- do s1 on s2, then union
  s1 `after` s2 = Map.map (subst s1) s2 `Map.union` s1

instance Subst TypeVariable where
  -- data Substitution TypeVariable = SU (Map TypeVariable Type) deriving (Show, Eq)
  wrap c = c

  subst m t@(VarTy a) = fromMaybe t (Map.lookup a m)
  subst m (FunTy s1 s2) = FunTy (subst m s1) (subst m s2)
  subst s (Forall vs t) =
    -- remove bound variables from substitution
    let newS = Map.withoutKeys s (Set.fromList vs)
        resTy = subst newS t
     in Forall vs resTy
  subst s (TyCstr tc vec) = TyCstr tc (fmap (subst s) vec)
  subst _ t = t

  freeV = fv

  s1 `after` s2 = Map.map (subst s1) s2 `Map.union` s1

-- | substitute out all instantiation variables for fresh unification (type) variables
substInstToUni :: Foldable f => f InstVariable -> TcMonad (Substitution InstVariable)
substInstToUni =
  foldM
    ( \acc x -> do
        a <- fresh
        return (Map.insert x (VarTy a) acc)
    )
    emptySubst

{-
==================================================================
                        Variables
==================================================================

We work with three different kinds of variables: term level
'Variable', unification 'TypeVariable', and instantiation
'InstVariable'.

In this section, we define some useful methods for working with
these variables.
-}

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

-- | Looks up a variable in a context
tLookup :: MonadError String m => Variable -> Map Variable a -> m a
tLookup x env = do
  case Map.lookup x env of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound variable " ++ x

-- | Fold over a type (used to implement 'fiv' and 'fv')
foldTy :: Monoid m => (Type -> Maybe m) -> Type -> m
foldTy f ty = case f ty of
  Just m -> m
  Nothing -> contFold f ty
  where
    contFold f (FunTy ty1 ty2) = foldTy f ty1 <> foldTy f ty2
    contFold f (Forall _ ty) = foldTy f ty
    contFold f (TyCstr _ args) = foldMap (foldTy f) args
    contFold _ _ = mempty

-- | Looks for the free instantiation variables of a type
fiv :: Type -> Set InstVariable
fiv = foldTy fivFolder
  where
    fivFolder :: Type -> Maybe (Set InstVariable)
    fivFolder (IVarTy v) = Just (Set.singleton v)
    fivFolder _ = Nothing

-- | Finds all FIVs in a list of types
fivs :: [Type] -> Set InstVariable
fivs = foldMap fiv

-- | Looks for free unification variables of a type
fv :: Type -> Set TypeVariable
fv = foldTy fvFolder
  where
    fvFolder (VarTy v) = Just $ Set.singleton v
    fvFolder (Forall vs ty) =
      let res = fv ty
       in return $ res `Set.difference` Set.fromList vs
    fvFolder _ = Nothing

{-
==================================================================
                        Type Checking
==================================================================

Alright, we're ready to get into the real tofu of all this. The
bidirectional type inference system is composed of two
judgements: 'checkType' and 'inferType'.

'checkType' is used to push information "down" from what we already
know while 'inferType' pushes information "up" from syntax. These
functions are mutually recursive.

You'll notice that in the 'App' cases, we use an 'instantiate'
judgement. This judgement takes in a head type and a list of
expressions applied to the head, and returns (if successful)
a result type and a list of types for the expressions. Details
to come in the next section
-}

inferType :: TypeEnv -> Expression -> TcMonad Type
-- LAMBDA
inferType env (Lam x e) = do
  argTy <- VarTy <$> fresh
  resTy <- inferType (env |: (x, argTy)) e
  return (FunTy argTy resTy)
-- APP
inferType env (App h es) = do
  -- infer type of head
  headTy <- inferType env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- generate a substitution to get rid of instantiation vars
  let together = resTy : argTys
  sub <- substInstToUni (fivs together)
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys) (\(e, t) -> checkType env e (subst sub t))
  return $ subst sub resTy

-- from application head type inference judgement
inferType env (Var v) = tLookup v (getExpVars env)
inferType env (Annot e t) = do
  checkType env e t
  return t
inferType _ (C (DC _ ty)) = return ty -- // TODO: check if ty is actually a type
-- // TODO: all other types of types

-- PRIMITIVES
inferType _ (IntExp _) = return IntTy
inferType _ (BoolExp _) = return BoolTy
inferType env (Op b e1 e2) = do
  t1 <- inferType env e1
  t2 <- inferType env e2
  equate t1 IntTy
  equate t2 IntTy
  if b == Plus || b == Times || b == Minus
    then return IntTy
    else return BoolTy

-- CASE
inferType env (Case e pes) = do
  -- infer type of argument
  ty <- inferType env e
  -- now for each case branch, check its type
  tys <-
    mapM
      ( \(pat, exp) -> do
          newEnv <- instantiateCase [ty] [pat]
          inferType (env <> newEnv) exp
      )
      pes
  -- fresh type variable
  alpha <- VarTy <$> fresh
  -- make sure every type is equal
  mapM_ (equate alpha) tys
  return alpha
-- foldM
--   ( \ty1 ty2 ->
--       evalStateT
--         ( do
--             ity1 <- inst ty1
--             ity2 <- inst ty2
--             -- // TODO: skolemize
--             sub <- lift $ mguQL ity1 ity2
--             let sty1 = subst sub ity1
--                 sty2 = subst sub ity2
--             equate sty1 sty2
--             return sty2
--         )
--         (IV 'K')
--   )
--   (head tys) -- UNSAFE
--   tys
inferType env (Let x e1 e2) = do
  tv <- fresh
  let xTy = VarTy tv
  resTy <- generalize env $ inferType (env |: (x, xTy)) e1
  let innerTy = case resTy of
        Forall vs ty -> ty
        ty -> ty
  equate innerTy xTy
  inferType (env |: (x, resTy)) e2
inferType _ _ = error "Unimplemented"

-- | 'checktype env e ty' succeeds if e can be checked to to have
-- type ty and fails otherwise. It also generates necessary
-- constraints
checkType :: TypeEnv -> Expression -> Type -> TcMonad ()
-- GEN
checkType (TE es as) e (Forall vs t) = checkType newEnv e t
  where
    -- add the quantified variables to the context
    newEnv = TE es (as <> Set.fromList vs)
-- LAMBDA CASES
checkType (TE es as) (Lam x e) (FunTy s1 s2) = checkType newEnv e s2
  where
    -- add the argument to the context
    newEnv = TE (Map.insert x s1 es) as
checkType env (Lam x e) t@(VarTy _) = do
  -- generate fresh type variables for the argument and return types
  argTy <- fresh
  resTy <- fresh
  -- t ~ argTy -> resTy
  equate t (FunTy (VarTy argTy) (VarTy resTy))
  -- do the usual lambda check
  let newEnv = env |: (x, VarTy argTy)
  checkType newEnv e (VarTy resTy)
checkType _ e@(Lam _ _) ty = throwError $ "Invalid type for lambda at: " <> display e <> " TYPE: " <> show ty -- // TODO: replace with pretty print
-- APP
checkType env (App h es) ty = do
  -- infer type of head
  headTy <- inferType env h
  -- perform quick look instantiation
  (argTys, resTy) <- instantiate env headTy es
  -- unify with the expected type
  sub1 <- mguQL resTy ty
  -- perform substitutions
  let argTys' = map (subst sub1) argTys
      resTy' = subst sub1 resTy
      -- generate a substitution to get rid of instantiation vars
      together = resTy' : argTys'
  sub2 <- substInstToUni (fivs together)
  -- equate with the expected type
  equate (subst sub2 resTy') ty
  -- generate the requisite constraints for the argument types
  forM_ (zip es argTys') (\(e, t) -> checkType env e (subst sub2 t))
-- PRIMITIVES
checkType _ (IntExp _) ty
  | isMono ty = equate ty IntTy
checkType _ (BoolExp _) ty
  | isMono ty = equate ty BoolTy
checkType env (Op b e1 e2) ty = do
  -- make sure e1 and e2 are ints
  checkType env e1 IntTy
  checkType env e2 IntTy
  if b == Plus || b == Times || b == Minus
    then equate ty IntTy
    else equate ty BoolTy
-- USER DEFINED TYPES STUFF
checkType env (C dc) ty = checkType env (App (C dc) []) ty -- just wrap in an App and use that case
-- CASE
checkType env (Case e pes) retTy = do
  -- infer type of argument
  ty <- inferType env e
  -- check the type of each branch
  mapM_
    ( \(pat, exp) -> do
        newEnv <- instantiateCase [ty] [pat]
        checkType (env <> newEnv) exp retTy
    )
    pes
checkType env e@(Annot _ _) ty' = checkType env (App e []) ty'
checkType env e@(Var _) ty' = checkType env (App e []) ty'
-- // TODO: all other cases
checkType env e ty = throwError $ "Fail checkType: " <> show env <> " EXP: " <> show e <> " TYPE: " <> show ty

{-
==================================================================
                        Instantiation
==================================================================

This is the real meat of things. What makes the Quick Look method
work. Instantiation proceeds recursively along the spine of
expressions.
Cases:
  - IALL: if the type is universally quantified, then generate a
          an instantiation variable for it
  - IARG: if the type is a function ty1 -> ty2, then take a "quick
          look" at the expression it's being typed against. This
          means that if there is some relevant "information" in
          the expression, 'qlArgument' will use that to generate
          a substitution
  - IVAR: 1) if the type is a unification variable, then generate
          fresh unification variables and continue with those
          2) if the type is an instantiation variable, then
          generate fresh instantiation variables and a
          substitution replacing with the new vars

The 'IARG' case mentions a "quick look" judgement. The purpose
of this judgement is to extract some sort of "knowledge" out
of the term through a substitution.
-}

-- | Wrapper for 'instantiateAux' which takes ignores the substitution
instantiate :: TypeEnv -> Type -> [Expression] -> TcMonad ([Type], Type)
instantiate env sTy es = do
  (_, sTys, ty) <- evalStateT (instantiateAux env sTy es) (IV 'K')
  return (sTys, ty)

-- | 'instantiateAux' env ty es
-- performs quick look instantiation returning a result type and list of
-- expression types; carries around a substitution for keeping track of
-- learned knowledge
instantiateAux :: TypeEnv -> Type -> [Expression] -> InstMonad (Substitution InstVariable, [Type], Type)
-- IALL - generate instantiation variable
instantiateAux env (Forall (v : vs) ty) es = do
  -- generate fresh variables and substitution
  iv <- freshIV
  let sub = Map.singleton v (IVarTy iv)
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
      sub1 = Map.singleton v newType
  -- check with new type
  (sub2, argTys, resTy) <- instantiateAux env newType (e : es)
  -- combine the substitutions
  return (sub2 `after` sub1, argTys, resTy)
instantiateAux _ ty [] = return (emptySubst, [], ty)
instantiateAux env ty es = throwError $ "Fail: " <> show env <> "  TYPE: " <> display ty <> "  EXP: " <> show (map display es)

-- | Takes a quick look at an expression. If it is guarded or has no free instantiation variables
-- then we're free to substitute
qlArgument :: TypeEnv -> Expression -> Type -> InstMonad (Substitution InstVariable)
qlArgument env e pTy =
  catchError
    ( do
        -- infer type of head
        hTy <- qlHead env h
        (_, retTy) <- lift $ instantiate env hTy es
        if isGuarded pTy || noFIVs retTy
          then lift $ mguQL pTy retTy
          else return emptySubst
    )
    (\_ -> return emptySubst) -- ignore errors in qlArgument, instead just return an empty substitution
  where
    (h, es) = case e of
      App h es -> (h, es)
      e' -> (e', []) -- if it's an arbitrary expression, pretend it's a nullary application

    -- check if a type is guarded under a type constructor
    isGuarded :: Type -> Bool
    isGuarded (FunTy _ _) = True
    isGuarded TyCstr {} = True
    isGuarded _ = False

    noFIVs :: Type -> Bool
    noFIVs t = null (fiv t)

-- | Looks at the head to see if there's any easy information to be got
qlHead :: TypeEnv -> Expression -> InstMonad Type
qlHead env (Var v) = tLookup v (getExpVars env)
qlHead _ (Annot _ sTy) = return sTy
qlHead _ (C (DC _ ty)) = return ty
qlHead _ (IntExp _) = return IntTy
qlHead _ (BoolExp _) = return BoolTy
qlHead _ _ = throwError "Failure: ql head doesn't allow arbitrary expressions (?)"

-- | Takes a pattern and a type and returns a new context with free variables bound
instantiateCase :: [Type] -> [Pattern] -> TcMonad TypeEnv
instantiateCase (ty : tys) (VarP x : xs) = do
  resEnv <- instantiateCase tys xs
  return $ resEnv |: (x, ty)
instantiateCase (ty : tys) (P (DC _ cTy) ps : xs) = do
  --
  -- -- get type of constructor
  cTy <- evalStateT (inst cTy) (IV 'K')
  let tys' = typeToList cTy
  -- throwError ("instCase: " <> show tys')
  (tys'', retTy) <- splitLast tys'
  -- unify data constructor return type and actual type
  sub <- mguQL retTy ty
  -- throwError $ "infer case tys: " <> show retTy <> " " <> show ty
  -- perform substitution on remaining stuff
  let tys3 = map (subst sub) tys''
  -- check this constructor
  env1 <- instantiateCase tys3 ps
  env2 <- instantiateCase tys xs
  return (env1 <> env2)
instantiateCase [] [] = return emptyEnv
instantiateCase tys ps = throwError $ "Fail instantiateCase: " <> show tys <> " " <> show ps

-- | Splits an array into front and last inside an error monad
splitLast :: MonadError String m => [a] -> m ([a], a)
splitLast [] = throwError "Bro empty list"
splitLast [x] = return ([], x)
splitLast (x : xs) = do
  (front, tail) <- splitLast xs
  return (x : front, tail)

-- | Generates something in the form of a -> a -> .... -> a
genUniformFun :: MonadError [Char] m => TypeVariable -> Nat -> m Type
genUniformFun _ Z = throwError "No good"
genUniformFun v (S Z) = return $ VarTy v
genUniformFun v (S n) = FunTy (VarTy v) <$> genUniformFun v n

--     undefined

typeToList :: Type -> [Type]
typeToList = foldTy tTLFolder
  where
    tTLFolder (FunTy _ _) = Nothing
    tTLFolder t = Just [t]

-- | instantiate a Forall type with Instantiation variables
inst :: Type -> InstMonad Type
inst (Forall (v : vs) ty) = do
  iv <- freshIV
  let sub = Map.singleton v (IVarTy iv)
  inst (subst sub (Forall vs ty))
inst (Forall [] ty) = return ty
inst ty = return ty

-- return undefined
{-
==================================================================
                  Putting things together
==================================================================

-}

-- | finds the most general unifier for poly types
-- mguQL :: Type -> Type -> TcMonad (Substitution InstVariable)
mguQL :: Type -> Type -> TcMonad (Substitution InstVariable)
mguQL t1 (IVarTy (IV v)) = varAsgn v t1
mguQL (IVarTy (IV v)) t2 = varAsgn v t2
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
            emptySubst
            (zipWith (,) vec1 vec2)
        else throwError $ "Incompatible type constructors " <> show tc1 <> " and " <> show tc2
    _ -> throwError $ "Incompatible type constructors " <> show tc1 <> " and " <> show tc2
mguQL (Forall vs1 ty1) (Forall vs2 ty2) = mguQL ty1 ty2
-- let res = mguQL ty1 ty2
--  in do
--       (sub, cstrts) <- listen res
--       case solve cstrts of -- ensure cstrts are solvable
--         Left err -> throwError err
--         Right _ -> return undefined
-- ensure

--         return undefined
-- weirder stuff
-- mguQL t1@(VarTy _) t2
--   | isMono t2 = equate t1 t2 >> return emptySubst
--   | otherwise = throwError "Types don't unify"
-- mguQL t1 t2@(VarTy _)
--   | isMono t2 = equate t1 t2 >> return emptySubst
--   | otherwise = throwError "Types don't unify"
-- mguQL IntTy IntTy = return emptySubst
-- mguQL BoolTy BoolTy = return emptySubst
mguQL _ _ = return emptySubst

-- mguQL t1 t2 = throwError $ "Types don't unify: " <> show t1 <> " " <> show t2

-- | Performs most general unification on mono-types. Used after inferType
mgu :: Type -> Type -> Either String (Substitution TypeVariable)
-- mgu ty1 ty2
--   | not (isMono ty1) || not (isMono ty2) = throwError "yo fuck. non mono-types somehow got to mgu"
mgu IntTy IntTy = return emptySubst
mgu BoolTy BoolTy = return emptySubst
mgu (FunTy l r) (FunTy l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (subst s1 r) (subst s1 r')
  return $ s2 `after` s1
mgu (VarTy a) t = varAsgn a t -- // TODO: do we need to inforce mono here?
mgu t (VarTy a) = varAsgn a t
mgu (TyCstr tc1 vec1) (TyCstr tc2 vec2) =
  case tc1 `testEquality` tc2 of
    Just Refl ->
      foldM
        ( \acc (ty1, ty2) -> do
            sbst <- mgu ty1 ty2
            return (acc `after` sbst)
        )
        emptySubst
        (zipWith (,) vec1 vec2)
    Nothing -> throwError "type constructors are different; don't unify"
mgu (Forall xs ty1) (Forall ys ty2)
  | length xs == length ys = mgu ty1 ty2
mgu ty1 ty2 = throwError $ "types don't unify " <> show ty1 <> " " <> show ty2

-- | Calls inferTy to generate a type and the constraints
genConstraints :: TypeEnv -> Expression -> Either String (Type, [Constraint])
genConstraints env = runTc . inferType env

-- | Solve a list of constraints. Used after inferType
solve :: [Constraint] -> Either String (Substitution TypeVariable)
solve =
  foldM
    ( \s1 (Equal t1 t2) -> do
        s2 <- mgu (subst s1 t1) (subst s1 t2)
        return (s2 `after` s1)
    )
    emptySubst

-- | Really puts everything together. Goes from an environment
-- and expression to either a type of an error.
typeInference :: TypeEnv -> Expression -> Either String Type
typeInference env e = do
  (ty, constraints) <- genConstraints env e
  -- throwError $ display ty <> " CSTRS: " <> show constraints
  s <- solve constraints
  return (subst s ty)

top :: FilePath -> IO ()
top fp = do
  exp <- parseFile fp
  let res = typeInference emptyEnv exp
  print res

exp =
  Let
    "head"
    ( Annot
        ( Lam
            "l"
            ( Case
                (Var "l")
                [(P (DC {getDCName = "Nil", getType = Forall "a" (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))}) [], C (DC {getDCName = "Nothing", getType = Forall "a" (TyCstr (TC "Maybe" (SS SZ)) (VarTy 'a' ::: VNil))})), (P (DC {getDCName = "Cons", getType = Forall "a" (FunTy (VarTy 'a') (FunTy (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil)) (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))))}) [VarP "x", VarP "xs"], App (C (DC {getDCName = "Just", getType = Forall "a" (FunTy (VarTy 'a') (TyCstr (TC "Maybe" (SS SZ)) (VarTy 'a' ::: VNil)))})) [Var "x"])]
            )
        )
        (Forall "a" (FunTy (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil)) (TyCstr (TC "Maybe" (SS SZ)) (VarTy 'a' ::: VNil))))
    )
    ( App
        (Var "head")
        [ App
            ( C
                ( DC
                    { getDCName = "Cons",
                      getType = Forall "a" (FunTy (VarTy 'a') (FunTy (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil)) (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))))
                    }
                )
            )
            [ IntExp 1,
              C
                ( DC
                    { getDCName = "Nil",
                      getType = Forall "a" (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))
                    }
                )
            ]
        ]
    )

-- | Used by Eval to filter ill-typed expressions
isValid :: Expression -> Bool
isValid = undefined

-- | Take a type, solve current constraints, and add Foralls for unbound variables
generalize :: TypeEnv -> TcMonad Type -> TcMonad Type
generalize env m = do
  (ty, constraints) <- listen m
  case solve constraints of
    Left err -> throwError err
    Right s -> do
      let sty = subst s ty
      let fvs = fv sty `minus` getTypeVars (substEnv s env)
      return (Forall (Set.toList fvs) sty)

minus :: Ord a => Set a -> Set a -> Set a
minus = Set.foldr Set.delete

-- TESTING
-- bunch of test cases

-- GOOD CASES
-- let f = \x -> x in (f 1)

{-
==================================================================
                  Test Cases and Examples
==================================================================
-}

good1 = Let "f" (Lam "x" (var "x")) (App (Var "f") [IntExp 1])

-- test constraint solving:
-- let f = \x -> x + 1 in (f 1)
good2 = Let "f" (Lam "x" (Op Plus (var "x") (IntExp 1))) (App (Var "f") [IntExp 1])

-- test Spine based application
-- (\x,y -> x + y) 1 2
good3 = App (Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1, IntExp 2]

-- test polymorphism
-- let f = \x -> x in let a = f True in f 1
good4 = Let "f" (Lam "x" (App (Var "x") [])) (Let "a" (App (Var "f") [IntExp 1]) (App (Var "f") [BoolExp True]))

-- partial application
-- (\x, y -> x + y) 1
good5 = App (Lam "x" (Lam "y" (Op Plus (var "x") (var "y")))) [IntExp 1]

-- BAD CASES
-- bad operator parameters
bad1 = Op Plus (IntExp 1) (BoolExp True)

-- wrong shape
bad2 = App (Lam "x" (Op Plus (var "x") (IntExp 1))) [IntExp 1, IntExp 2]

testTypeInf =
  TestList
    [ -- good
      typeInference emptyEnv good1 ~?= Right IntTy,
      typeInference emptyEnv good2 ~?= Right IntTy,
      typeInference emptyEnv good3 ~?= Right IntTy,
      typeInference emptyEnv good4 ~?= Right BoolTy,
      typeInference emptyEnv good5 ~?= Right (FunTy IntTy IntTy),
      -- bad
      typeInference emptyEnv bad1 ~?= Left "bad operator parameters",
      typeInference emptyEnv bad2 ~?= Left "function applied to too many arguments"
    ]

-- EXAMPLES AND FUN
listTC :: TypeConstructor (S Z)
listTC = TC "List" (SS SZ)

listTy :: TypeVariable -> Type
listTy v = TyCstr listTC (VarTy v ::: VNil)

consTy :: Type
consTy = Forall ['a'] (FunTy (VarTy 'a') (FunTy (listTy 'a') (listTy 'a')))

nilTy :: Type
nilTy = Forall ['a'] (TyCstr listTC (VarTy 'a' ::: VNil))

consDC :: DataConstructor
consDC = DC "cons" consTy

nilDC :: DataConstructor
nilDC = DC "nil" nilTy

consExp :: Expression
consExp = C consDC

nilExp :: Expression
nilExp = C nilDC

ex1 :: Expression
ex1 = App consExp [IntExp 1, nilExp]

-- polymorphism example (id : ids) -- WORKS!
idTy :: Type
idTy = Forall ['b'] (FunTy (VarTy 'b') (VarTy 'b'))

idsTy :: Type
idsTy = TyCstr listTC (idTy ::: VNil)

idsCtx :: TypeEnv
idsCtx = TE (Map.fromList [("id", idTy), ("ids", idsTy)]) Set.empty

ex2 :: Expression
-- id :: forall a. a -> a
-- ids :: [forall a. a -> a]
-- Cons id Nil :: (forall a [a -> a])
-- id : ids
-- Cons :: a -> List a -> List a
-- (forall a. a -> a) -> List (forall .....)
ex2 = App consExp [var "id", var "ids"]

-- PATTERN MATCHING EXAMPLES
{-
case [1] of
  nil -> \y -> 0
  (x : xs) -> 1
-}
exCase :: Expression
exCase = Case ex1 [(P nilDC [], IntExp 0), (P consDC [VarP "x", VarP "xs"], IntExp 1)]

exCase1 :: Expression
exCase1 = Case ex1 [(P consDC [VarP "x", VarP "xs"], Var "x"), (P nilDC [], Lam "y" (Var "y"))]

exCase2 :: Expression
exCase2 = Case ex2 [(P consDC [VarP "x", VarP "xs"], Var "x"), (P nilDC [], Lam "y" (Var "y"))]

exCase2' :: Expression
exCase2' = App exCase1 [IntExp 1]

runTc :: TcMonad a -> Either String (a, [Constraint])
runTc m = evalStateT (runWriterT m) 'a'

-- MISCELLANEOUS
ex =
  Let
    "id"
    ( Annot
        (Lam "x" (Var "x"))
        (Forall "a" (FunTy (VarTy 'a') (VarTy 'a')))
    )
    ( Let
        "ids"
        ( Annot
            (App (C (DC {getDCName = "Cons", getType = Forall "a" (FunTy (VarTy 'a') (FunTy (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil)) (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))))})) [Var "id", C (DC {getDCName = "Nil", getType = Forall "a" (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))})])
            (TyCstr (TC "List" (SS SZ)) (Forall "a" (FunTy (VarTy 'a') (VarTy 'a')) ::: VNil))
        )
        ( App
            (C (DC {getDCName = "Cons", getType = Forall "a" (FunTy (VarTy 'a') (FunTy (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil)) (TyCstr (TC "List" (SS SZ)) (VarTy 'a' ::: VNil))))}))
            [Var "id", Var "ids"]
        )
    )