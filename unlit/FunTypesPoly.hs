{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unused-binds -Wno-unused-matches
      -Wno-name-shadowing -Wno-missing-signatures #-}

module FunTypesPoly where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import FunEnvError
import FunSyntax
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP

data Type
  = IntTy -- i.e. 'Int'
  | BoolTy -- i.e. 'Bool'
  | FunTy Type Type -- i.e. t1 -> t2
  | VarTy TypeVariable -- we'll get to this later
  deriving (Eq, Show)

instance PP Type where
  pp (VarTy i) = PP.text [i]
  pp (FunTy t1@(FunTy _ _) t2) = (PP.parens (pp t1)) <+> PP.text "->" <+> pp t2
  pp (FunTy t1 t2) = pp t1 <+> PP.text "->" <+> pp t2
  pp IntTy = PP.text "Int"
  pp BoolTy = PP.text "Bool"

type TypeVariable = Char

type TypeEnv = Map Variable Scheme

tLookup :: MonadError String m => Variable -> Map Variable a -> m a
tLookup x env = do
  case (Map.lookup x env) of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound variable " ++ x

inferTySimple :: Expression -> Map Variable Type -> Either String Type
inferTySimple (Var x) env = tLookup x env
inferTySimple (IntExp _) env = return $ IntTy
inferTySimple (BoolExp _) env = return $ BoolTy
inferTySimple (If e1 e2 e3) env = do
  t1 <- inferTySimple e1 env
  t2 <- inferTySimple e2 env
  t3 <- inferTySimple e3 env
  case t1 of
    BoolTy -> if t2 == t3 then return t2 else throwError "oops!"
    _ -> throwError "Must have a boolean in the condition of the if"
inferTySimple (Op b e1 e2) env = do
  t1 <- inferTySimple e1 env
  t2 <- inferTySimple e2 env
  when (t1 /= IntTy) $ throwError "First arg to an operator must be an Int"
  when (t2 /= IntTy) $ throwError "Second arg to an operator must be an Int"
  if b == Plus || b == Times || b == Minus
    then return IntTy
    else return BoolTy
inferTySimple (App e1 e2) env = do
  t1 <- inferTySimple e1 env
  t2 <- inferTySimple e2 env
  case t1 of
    FunTy a b -> if t2 == a then return b else throwError "type mismatch"
    _ -> throwError "not a function, cannot apply"

{-  Doesn't work!
inferTySimple (Fun x e) env = do
   t2 <- inferTySimple e (Map.insert x ?? env)
   return $ FunTy ?? t2
 -}

prelude =
  Map.fromList
    [ ("NOT", FunTy BoolTy BoolTy),
      ("AND", FunTy BoolTy (FunTy BoolTy BoolTy)),
      ("OR", FunTy BoolTy (FunTy BoolTy BoolTy))
    ]

simple1 = "1 + 3"

simple2 = "if 1 < 3 then 1 + 3 else 4 * 5"

simple3 = "if 1 < 3 then true else 4 * 5"

simple4 = "if (NOT true) then AND else OR"

simpleTop :: String -> IO ()
simpleTop s = case parseExp s >>= \e -> inferTySimple e prelude of
  Left err -> putStrLn err
  Right t -> putStrLn (s ++ " : " ++ show (pp t))

example0 = "fun X -> X + 1"

example1 = "fun X -> X"

example2 = "fun X -> fun Y -> X"

fresh :: TcMonad TypeVariable
fresh = do
  s <- get
  put $ succ s
  return s

example3 = "fun X -> X + 1"

data Constraint = Equal Type Type

equate :: Type -> Type -> TcMonad ()
equate t1 t2
  | t1 == t2 = return ()
  | otherwise = tell [Equal t1 t2]

type TcMonad a =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )
    a

runTc :: TcMonad a -> Either String (a, [Constraint])
runTc m = evalStateT (runWriterT m) 'a'

inferTy :: Expression -> TypeEnv -> TcMonad Type
inferTy (Var x) env = do
  scheme <- tLookup x env
  instantiate scheme
inferTy (IntExp _) env = return IntTy
inferTy (BoolExp _) env = return BoolTy
inferTy (If e1 e2 e3) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  t3 <- inferTy e3 env
  equate t1 BoolTy
  equate t2 t3
  return t2
inferTy (Op b e1 e2) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  equate t1 IntTy
  equate t2 IntTy
  if b == Plus || b == Times || b == Minus
    then return IntTy
    else return BoolTy
inferTy (Fun x e) env =
  do
    a <- fresh
    let argTy = Forall Set.empty (VarTy a)
    resTy <- inferTy e (Map.insert x argTy env)
    return (FunTy (VarTy a) resTy)
inferTy (App e1 e2) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  b <- fresh
  equate t1 (FunTy t2 (VarTy b))
  return (VarTy b)
inferTy (Let x e1 e2) env = do
  tv <- fresh
  let xTy = Forall Set.empty (VarTy tv)
  Forall vs ty <- generalize env $ inferTy e1 (Map.insert x xTy env) -- a -> a  =>  forall a.
  equate ty (VarTy tv)
  inferTy e2 (Map.insert x (Forall vs ty) env)

instance PP Constraint where
  pp (Equal t1 t2) = pp t1 <+> PP.text "=" <+> pp t2

genConstraints :: Expression -> Either String (Type, [Constraint])
genConstraints = runTc . (\e -> inferTy e Map.empty)

parseExp :: String -> Either String Expression
parseExp s = case parse s of
  Just e -> Right e
  Nothing -> Left "parse error"

putConstraints :: String -> IO ()
putConstraints s = case parseExp s >>= runTc . (\e -> inferTy e Map.empty) of
  Left err -> putStrLn err
  Right (t, c) ->
    putStrLn
      ( show
          ( PP.text s <+> PP.text ":" <+> pp t $$ PP.text "where"
              <+> (PP.vcat (map pp c))
          )
      )

example4 = "let F = fun X -> if X <= 1 then 1 else F (X - 1) in F"

example4a = "(fun X -> let Y = X in Y) 3"

example4b = "(fun F -> fun X -> F X + 1) (fun Y -> Y)"

example4c = "(fun F -> fun X -> F (F X)) (fun Y -> if Y then 1 else 0)"

data Substitution = Subst (Map TypeVariable Type) deriving (Show, Eq)

subst :: Substitution -> Type -> Type
subst (Subst s) t@(VarTy a) = case Map.lookup a s of
  Just ty -> ty
  Nothing -> (VarTy a)
subst s (FunTy t1 t2) = FunTy (subst s t1) (subst s t2)
subst s IntTy = IntTy
subst s BoolTy = BoolTy

empSubst :: Substitution
empSubst = Subst Map.empty

after :: Substitution -> Substitution -> Substitution
Subst s1 `after` Subst s2 = Subst $ (Map.map (subst (Subst s1)) s2) `Map.union` s1

s2 = Subst (Map.fromList [('a', IntTy)])

s1 = Subst (Map.fromList [('b', FunTy (VarTy 'a') BoolTy)])

mgu :: Type -> Type -> Either String Substitution
mgu IntTy IntTy = return empSubst
mgu BoolTy BoolTy = return empSubst
mgu (FunTy l r) (FunTy l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (subst s1 r) (subst s1 r')
  return $ s2 `after` s1
mgu (VarTy a) t = varAsgn a t
mgu t (VarTy a) = varAsgn a t
mgu _ _ = throwError $ "types don't unify"

varAsgn a t
  | t == VarTy a = return empSubst
  | a `Set.member` (fv t) =
    throwError $
      "occur check fails: " ++ show a ++ " in " ++ show t
  | otherwise = return $ Subst (Map.singleton a t)

fv :: Type -> Set TypeVariable
fv (VarTy v) = Set.singleton v
fv (FunTy t1 t2) = (fv t1) `Set.union` (fv t2)
fv IntTy = Set.empty
fv BoolTy = Set.empty

solve :: [Constraint] -> Either String Substitution
solve cs =
  foldM
    ( \s1 (Equal t1 t2) -> do
        s2 <- mgu (subst s1 t1) (subst s1 t2)
        return (s2 `after` s1)
    )
    empSubst
    cs

mgu_test1 = mgu (VarTy 'a') IntTy

mgu_test2 = mgu (VarTy 'a') (VarTy 'b')

mgu_test3 = mgu (FunTy (VarTy 'a') (VarTy 'b')) (FunTy (VarTy 'a') (VarTy 'd'))

mgu_test4 = mgu (FunTy (VarTy 'a') IntTy) (FunTy BoolTy (VarTy 'b'))

mgu_test5 = mgu IntTy IntTy

mgu_test6 = mgu IntTy BoolTy

mgu_test7 = mgu IntTy (FunTy (VarTy 'a') (VarTy 'b'))

mgu_test8 = mgu (VarTy 'a') (FunTy (VarTy 'a') (VarTy 'b'))

typeInference :: Expression -> Either String Type
typeInference e = do
  (ty, constraints) <- genConstraints e
  s <- solve constraints
  return (subst s ty)

top :: String -> IO ()
top s = case parseExp s >>= typeInference of
  Left err -> putStrLn err
  Right t -> putStrLn (s ++ " : " ++ show (pp t))

bad1 = "X + 1"

bad2 = "1 + true"

bad3 = "(fun X -> X + 1) true"

bad4 = "fun X -> X X"

example5 = "let Y = (fun X -> X) true in (fun X -> X) 3"

example6 = "let I = fun X -> X in let Y = I true in I 3"

example7a = "let I = fun X -> X in I I"

example7b = "let J = fun X -> X X in J"

data Scheme = Forall (Set TypeVariable) Type

instantiate :: Scheme -> TcMonad Type
instantiate (Forall vs ty) = do
  let combine s v = do
        x <- fresh
        return $ Subst (Map.singleton v (VarTy x)) `after` s
  s <- foldM combine empSubst (Set.toList vs)
  return (subst s ty)

example8 = "fun X -> let Y = X in Y + 1"

generalize :: TypeEnv -> TcMonad Type -> TcMonad (Scheme)
generalize env m = do
  (ty, constraints) <- listen m
  case (solve constraints) of
    Left err -> throwError err
    Right s -> do
      let sty = subst s ty
      let fvs = fv sty `minus` fvEnv (substEnv s env)
      return (Forall fvs sty)

substEnv :: Substitution -> TypeEnv -> TypeEnv
substEnv s env = Map.map (substs s) env

substs :: Substitution -> Scheme -> Scheme
substs s (Forall vs ty) = (Forall vs (subst s ty))

fvEnv :: TypeEnv -> Set TypeVariable
fvEnv m = Map.foldr gather Set.empty m
  where
    gather (Forall vs ty) s = fv ty `minus` vs `Set.union` s

minus :: Ord a => Set a -> Set a -> Set a
minus = Set.foldr Set.delete

example9 = "let I = fun X -> let Y = X in Y in I I"

example10 = "let I = fun X -> X in let F = fun X -> I X in F"

example11 = "let I = fun X -> X in let F = fun X -> let Y = I X in Y + 1 in F"
