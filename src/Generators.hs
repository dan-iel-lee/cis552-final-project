module Generators where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Either (isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vec.Lazy (Vec (VNil))
import Eval
import Parser ()
import Test.QuickCheck
import TypeInf
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
    total = Set.fromList $ (: []) <$> ['A' .. 'z']
    allowedS = total `Set.difference` bound

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
genExp ty ctx n = frequency $ n0 ++ ng0 ++ varGen ++ annotGen -- ++ appGenSmart
  where
    -- reduce size
    n' = n `div` 2
    -- can always surround with annotation or find a variable
    annotGen = [(0, (`Annot` ty) <$> genExp ty ctx n')]
    varGen =
      -- find variables with the given type
      -- // TODO: also variables which can be instantiated to the given type
      let validVars = Map.filter (== ty) ctx
       in case Map.keys validVars of
            [] -> []
            _ -> [(7, Var <$> arbVar validVars)]
    -- generate an application based on what's in the context
    appGenSmart =
      let splitCtx = fmap typeToList ctx
          validCtx = Map.filter (\ts -> last ts == ty) splitCtx
       in case Map.size validCtx of
            0 -> []
            _ ->
              [ ( 2,
                  do
                    (v, tys) <- elements (Map.toList validCtx)
                    args <- mapM (\ty -> genExp ty ctx n') (allButLast tys)
                    return (App (Var v) args)
                )
              ]
    -- helper for appGenSmart
    allButLast :: [a] -> [a]
    allButLast [y] = []
    allButLast (x : xs) = x : allButLast xs
    -- helper for var case
    -- tryInst
    -- Cases
    -- 1) n = 0
    -- if n = 0, only decrease the size of the type left to generate
    n0 = case ty of
      IntTy -> [(2, IntExp <$> arbNat)]
      BoolTy -> [(2, BoolExp <$> arbitrary)]
      FunTy t1 t2 ->
        [ ( 1,
            do
              x <- arbFreshVar ctx
              e <- genExp t2 (Map.insert x t1 ctx) n'
              return (Lam x e)
          )
        ]
      -- // NOTE: don't have to worry about type var scoping
      Forall _ ty' -> [(1, genExp ty' ctx n)]
      _ -> []

    -- 2) n > 0
    ng0 = case n of
      0 -> []
      _ -> ng0Specific ++ ng0All

    -- 2a) type specific cases (for ints and bools)
    ng0Specific = case ty of
      IntTy -> [(3, intOpGen)]
      BoolTy -> [(3, boolOpGen)]
      _ -> []

    -- 2b) in general, we can always surround by let, if, or app
    ng0All = [(2, letGen), (1, appGen), (2, ifGen), (2, caseGen)]
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
      ty' <- sized (genTypePol Neg) -- (arbitrary :: Gen Type) -- // NOTE: at the moment can't access any bound type variables
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

    appGen = do
      -- generate an arbitrary (small) natural number for argument count
      argCount <- (\n -> 1 + n `div` 5) <$> arbNat
      -- generate an arbitrary list of argument types
      tys <- replicateM argCount (arbitrary :: Gen Type)
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
        [ (4, funGen) -- ,
        -- (2, faGen)
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
    sized (genExp ty Map.empty)

  shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (If e1 e2 e3) = [If e1' e2' e3' | e1' <- shrink e1, e2' <- shrink e2, e3' <- shrink e3]
  shrink (Lam v e1) = [Lam v e1' | e1' <- shrink e1]
  shrink (App e1 e2) = [App e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Let v e1 e2) = [Let v e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Case e cs) = [Case e' cs | e' <- shrink e]
  shrink (Annot e _) = [e]
  shrink _ = []

instance Arbitrary Type where
  arbitrary = sized genType
  shrink _ = [] -- // TODO: how to shrink
