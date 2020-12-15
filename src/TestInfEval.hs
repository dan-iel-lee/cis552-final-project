{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TestInfEval where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Either (isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vec.Lazy (Vec (VNil))
import Eval2
import Parser ()
import Test.QuickCheck
import TypeInf
import Types

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
genExp ty ctx n = frequency $ n0 ++ ng0 ++ varGen ++ [annotGen]
  where
    -- reduce size
    n' = n `div` 2
    -- can always surround with annotation or find a variables
    annotGen = (1, (`Annot` ty) <$> genExp ty ctx n')
    varGen =
      -- find variables with the given type
      -- // TODO: also variables which can be instantiated to the given type
      let validVars = Map.filter (== ty) ctx
       in case Map.keys validVars of
            [] -> []
            _ -> [(7, Var <$> arbVar validVars)]
    -- Cases
    -- 1) n = 0
    -- if n = 0, only decrease the size of the type left to generate
    n0 = case ty of
      IntTy -> [(7, IntExp <$> arbNat)]
      BoolTy -> [(7, BoolExp <$> arbitrary)]
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
      IntTy -> [(1, intOpGen)]
      BoolTy -> [(1, boolOpGen)]
      _ -> []

    -- 2b) in general, we can always surround by let, if, or app
    ng0All = [(1, letGen), (1, appGen), (1, ifGen), (7, caseGen)]
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
      ty' <- (arbitrary :: Gen Type)
      -- insert (x, ty') into the context
      let newCtx = Map.insert x ty' ctx
      -- generate the e1 in "x = e1"
      e1 <- genExp ty' newCtx n'
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

-- // TODO: allow type variables
--            this is tricky, need to know what variables we're allowed to use
genType :: Int -> Gen Type
genType n = oneof $ n0 : ng0
  where
    n' = n `div` 2
    n0 = elements [IntTy, BoolTy]
    ng0 = case n of
      0 -> []
      _ ->
        [ FunTy <$> genType n' <*> genType n'
        ]

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

-- // TODO: allow for type variables

{-
===================================================
                Type Inf and Eval
===================================================
-}

-- if an expression is well typed, then it is either a value or it steps
progress :: Expression -> Property
progress e = isValid e ==> isValue e || isRight (step e)

preservation :: Expression -> Property
preservation e =
  -- if: e is well typed and not a value
  isValid e && not (isValue e)
    ==> let -- starting type
            ty1 = typeInference emptyEnv e
            -- type post step
            ty2 = do
              e' <- step e
              typeInference emptyEnv e'
         in -- then: types must be alpha equivalent
            case (ty1, ty2) of
              (Right ty1', Right ty2') -> isRight $ alphaEquiv ty1' ty2'
              _ -> False

quickCheckN :: (Testable prop) => Int -> prop -> IO ()
quickCheckN n = quickCheck . withMaxSuccess n