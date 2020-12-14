module TestInfEval where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Either (isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Vec.Lazy (Vec (VNil))
import Eval2
import Parser ()
import Test.HUnit
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

arbNat :: Gen Int
arbNat = fmap abs arbitrary

genExp :: Set Type -> GenCtx -> Int -> Gen Expression
genExp tys ctx 0 = case Map.keys ctx of
  [] ->
    oneof
      [ fmap IntExp arbNat,
        fmap BoolExp arbitrary
      ]
  _ ->
    oneof
      [ fmap Var (arbVar ctx),
        fmap IntExp arbNat,
        fmap BoolExp arbitrary
      ]
-- genExp :: Int -> Gen Expression
genExp tys ctx n =
  frequency
    [ (1, fmap Var (arbVar ctx)),
      (1, fmap IntExp arbNat),
      (1, fmap BoolExp arbitrary),
      (7, liftM3 Op arbitrary (genExp n') (genExp n')),
      (4, liftM2 Case (genExp n') patternList),
      (7, liftM2 Lam arbVar (genExp n')),
      (4, liftM2 App (genExp n') exprList),
      (7, liftM3 Let arbVar (genExp n') (genExp n'))
    ]
  where
    n' = n `div` 2
    patternList :: Gen [(Pattern, Expression)]
    patternList = foldr (liftM2 (:)) (return []) (replicate n' $ liftM2 (,) genPattern (genExp n'))
    exprList :: Gen [Expression]
    exprList = foldr (liftM2 (:)) (return []) $ replicate n' (genExp n')

-- genExp 0 =
--   oneof
--     [ fmap Var arbVar,
--       fmap IntExp arbNat,
--       fmap BoolExp arbitrary
--     ]
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
