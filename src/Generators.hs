module Generators where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Char as Char
import Data.Either (isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vec.Lazy (Vec (VNil))
import Test.QuickCheck
import TypeInf (instUV, mgu, runTc)
import Types
import Prelude hiding (flip)

{-
===================================================
                    Generators
===================================================
-}

type GenCtx = Map Variable Type

arbVar :: GenCtx -> Gen Variable
arbVar = elements . Map.keys

arbPattern :: Type -> GenCtx -> Gen Pattern
arbPattern ty ctx = case ty of
  IntTy -> frequency [(4, IntP <$> arbNat), (1, VarP <$> arbFreshVar ctx)]
  BoolTy -> frequency [(4, BoolP <$> arbitrary), (1, VarP <$> arbFreshVar ctx)]
  _ -> VarP <$> arbFreshVar ctx

arbFreshVar :: GenCtx -> Gen Variable
arbFreshVar ctx = elements $ Set.toList allowedS
  where
    bound = Set.fromList (Map.keys ctx)
    total = Set.fromList $ (: []) <$> ['a' .. 'z']
    allowedS = total -- `Set.difference` bound

-- instance Enum String where
--   toEnum n
--     | n < 26 = [toEnum (n + 97)]
--     | otherwise =
--       let rest = toEnum (n - 26)
--        in toEnum (n `mod` 26 + 97) : rest

arbNat :: Gen Int
arbNat = fmap abs arbitrary

genExp :: Type -> GenCtx -> Int -> Gen Expression
-- genExp IntTy _ 0 = IntExp <$> arbNat
-- genExp BoolTy _ 0 = BoolExp <$> arbitrary
-- // TODO: change to frequencies
genExp ty ctx n = frequency $
  case n of
    0 -> if null n0 then [(1, return (IntExp 1))] else n0
    _ -> ng0 --n0 ++ ng0 ++ varGen ++ annotGen ++ appGenSmart
  where
    -- reduce size
    n' = n `div` 2
    -- can always surround with annotation or find a variable
    annotGen = (`Annot` ty) <$> genExp ty ctx n'
    varGen =
      -- find variables with the given type
      -- // TODO: also variables which can be instantiated to the given type
      let validVars = Map.filter (`canInst` ty) ctx
       in case Map.keys validVars of
            [] -> []
            _ -> [(7, Var <$> arbVar validVars)]
    -- generate an application based on what's in the context
    -- // TODO: generate ALL return types
    appGenSmart =
      let splitCtx = fmap typeSplits ctx
          filtCtx = Map.map (filter (\ts -> last ts `canInst` ty)) splitCtx
          validCtx = Map.filter (not . null) filtCtx
          finalCtx = Map.map head validCtx
       in case Map.size finalCtx of
            0 -> []
            _ ->
              [ ( 3,
                  do
                    (v, tys) <- elements (Map.toList finalCtx)
                    args <- mapM (\ty -> genExp ty ctx n') (allButLast tys)
                    return (App (Var v) args)
                )
              ]
    -- check if a type can be instantiated to the correct type
    canInst :: Type -> Type -> Bool
    canInst t1 t2 = isRight $ do
      (t1', _) <- runTc $ instUV t1
      mgu t1' t2
    typeSplits :: Type -> [[Type]]
    typeSplits (FunTy l r) =
      [l, r] :
      ( do
          s <- typeSplits r
          return (l : s)
      )
    typeSplits t = return [t]
    -- helper for appGenSmart
    allButLast :: [a] -> [a]
    allButLast [y] = []
    allButLast (x : xs) = x : allButLast xs
    -- Cases
    -- 1) n = 0
    -- if n = 0, only decrease the size of the type left to generate
    n0Specific = case ty of
      IntTy -> [(10, IntExp <$> arbNat)]
      BoolTy -> [(10, BoolExp <$> arbitrary)]
      FunTy t1 t2 ->
        [ (10, funGen t1 t2)
        ]
      -- // NOTE: don't have to worry about type var scoping
      Forall _ ty' -> [(10, genExp ty' ctx n), (3, annotGen)]
      _ -> []
    n0 = n0Specific ++ varGen ++ appGenSmart

    funGen t1 t2 = do
      x <- arbFreshVar ctx
      e <- genExp t2 (Map.insert x t1 ctx) n'
      return (Lam x e)

    -- 2) n > 0
    ng0 = ng0Specific ++ ng0All ++ appGenSmart ++ varGen ++ [(1, annotGen)]

    -- 2a) type specific cases (for ints and bools)
    ng0Specific = case ty of
      IntTy -> [(2, IntExp <$> arbNat), (3, intOpGen)]
      BoolTy -> [(3, BoolExp <$> arbitrary), (3, boolOpGen)]
      FunTy t1 t2 ->
        [ (3, funGen t1 t2)
        ]
      -- // NOTE: don't have to worry about type var scoping
      Forall _ ty' -> [(10, genExp ty' ctx n)]
      _ -> []

    -- 2b) in general, we can always surround by let, if, or app
    ng0All = [(1, letGen), (1, appGen), (2, ifGen), (2, caseGen)]
    -- generate an operation which returns an Int

    intOpGen = do
      op <- elements [Plus .. Times]
      a <- genExp IntTy ctx n'
      b <- genExp IntTy ctx n'
      return (Op op a b)
    -- generate an operation which returns a Bool
    boolOpGen = do
      op <- elements [Gt .. Le]
      a <- genExp IntTy ctx n'
      b <- genExp IntTy ctx n'
      return (Op op a b)

    letGen = do
      -- get a fresh variable
      x <- arbFreshVar ctx
      -- generate a type for x
      ty' <- mTyGen -- (arbitrary :: Gen Type) -- // NOTE: at the moment can't access any bound type variables
      -- insert (x, ty') into the context
      let newCtx = Map.insert x ty' ctx
      -- generate the e1 in "x = e1"
      e1 <- genExp ty' newCtx n' -- // TODO: make this not hacky
      -- generate the body
      e2 <- genExp ty newCtx n'
      return (Let x e1 e2)

    ifGen = do
      bexp <- genExp BoolTy ctx n'
      e1 <- genExp ty ctx n'
      e2 <- genExp ty ctx n'
      return (If bexp e1 e2)

    -- generates a pattern given the desired pattern type and expression result type
    patternExprGen :: Type -> Type -> GenCtx -> Gen (Pattern, Expression)
    patternExprGen pTy resTy ctx' = do
      -- generate some patterns + at least one wildcard variables
      p <- arbPattern pTy ctx'
      -- Yikes, couldn't write this in a cleaner way
      let newCtx = (case p of VarP x -> Map.insert x pTy ctx'; _ -> ctx')
      -- generate result of match
      res <- genExp resTy newCtx n'
      return (p, res)

    -- do casing here
    caseGen = do
      -- generate an expression to case over, must be a super simple type
      pTy <- elements [IntTy, BoolTy]
      e1 <- genExp pTy ctx n'

      -- replicate an obscure number of patterns with a wildcard
      let count = 1
      patterns <- replicateM count (patternExprGen pTy ty ctx)

      -- makes sure to add a variable wildcard so case never fails
      x <- arbFreshVar ctx
      wildE <- genExp ty (Map.insert x pTy ctx) n'
      let patterns' = patterns ++ [(VarP x, wildE)]

      return (Case e1 patterns')

    mTyGen = resize n' (sized genTypeMono)

    appGen = do
      -- generate an arbitrary (small) natural number for argument count
      argCount <- (\n -> 1 + n `div` 5) <$> arbNat
      -- generate an arbitrary list of argument types
      tys <- replicateM argCount mTyGen
      -- combine into one type for the head
      let headTy = foldr FunTy ty tys
      -- generate head (at 0 so that there's no nested Apps)
      head <- genExp headTy ctx 0
      -- generate argument expressions by type
      args <- mapM (\ty' -> genExp ty' ctx n') tys
      return (App head args)

type GenTyCtx = Set TypeVariable

data Polarity = Pos | Neg

flip :: Polarity -> Polarity
flip Pos = Neg
flip Neg = Pos

-- // TODO: allow type variables
--            this is tricky, need to know what variables we're allowed to use

genTypeMono :: Int -> Gen Type
genTypeMono n = frequency $ n0 ++ ng0
  where
    n' = n `div` 2
    n0 = [(1, return IntTy), (1, return BoolTy)]
    ng0 = case n of
      0 -> []
      _ ->
        [ (4, FunTy <$> genTypeMono n' <*> genTypeMono n')
        ]

genType :: Int -> Gen Type
genType = genTypePol Pos

genTypePol :: Polarity -> Int -> Gen Type
genTypePol = genTypeAux Set.empty Set.empty

-- f :: Int -> Int -> a
-- f n m = f n m

-- Int -> a
-- a -> b -> a
f :: ((a -> Int) -> b) -> b
f g = g (const 1)

-- (a -> Int) -> a

-- (a -> Int) -> Int
fun :: (a -> Int) -> a
fun = fun

-- ((a -> Int) -> b) -> b

genTypeAux :: Set TypeVariable -> Set TypeVariable -> Polarity -> Int -> Gen Type
genTypeAux env argctx p n = frequency $ n0 ++ ng0 ++ varGen
  where
    n' = n `div` 2
    n0 = [(1, return IntTy), (1, return BoolTy)]
    varGen =
      let vEnv =
            case p of
              Pos -> argctx
              Neg -> env
       in case Set.size vEnv of
            0 -> []
            _ -> [(4, VarTy <$> elements (Set.toList vEnv))]
    ng0 = case n of
      0 -> []
      _ ->
        [ (4, funGen),
          (2, faGen)
        ]
    funGen = do
      -- generate an arg type with Positivity reversed
      ty1 <- genTypeAux env argctx (flip p) n'
      -- if the return type is a variable, then we add that to argctx
      let ret = getPos ty1
          newArgctx = case ret of
            VarTy v -> Set.insert v argctx
            _ -> argctx
      -- generate return type with new argctx
      ty2 <- genTypeAux env newArgctx p n'
      return (FunTy ty1 ty2)

    getPos (FunTy _ r) = getPos r
    getPos ty = ty

    faGen = do
      vars <- faVarGen n'
      let newEnv = env `Set.union` Set.fromList vars
      body <- genTypeAux newEnv argctx p n'
      return (Forall vars body)
    faVarGen n =
      frequency
        [ (1, (: []) <$> charGen),
          (n, (:) <$> charGen <*> faVarGen (n `div` 2))
        ]
    charGen = elements ['a' .. 'z']

-- forall a. a
-- let x = x in x
instance Arbitrary Expression where
  arbitrary = do
    ty <- arbitrary
    scale (`div` 3) $ sized (genExp ty Map.empty)

  shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (If e1 e2 e3) = [If e1' e2' e3' | e1' <- shrink e1, e2' <- shrink e2, e3' <- shrink e3]
  shrink (Lam v e1) = [Lam v e1' | e1' <- shrink e1]
  shrink (App e1 e2) = [App e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Let v e1 e2) = [Let v e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Case e cs) = [Case e' cs | e' <- shrink e]
  shrink (Annot e _) = [e]
  shrink _ = []

instance Arbitrary Type where
  arbitrary = scale (`div` 2) $ sized genType
  shrink _ = []
