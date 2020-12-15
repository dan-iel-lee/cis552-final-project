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
import Eval
import Generators
import Parser ()
import Test.QuickCheck
import TypeInf
import Types

-- // TODO: allow for type variables

{-
===================================================
                Type Inf and Eval
===================================================
-}

-- | if an expression is well typed, then it is either a value or it steps
progress :: Expression -> Property
progress e = isValid e ==> isValue e || isRight (step e)

-- | if an expression is well typed and not a value
-- then its type is preserved after a step
preservation :: Expression -> Property
preservation e =
  -- if: e is well typed and not a value
  isValid e && not (isValue e)
    ==> isRight
    $ do
      -- infer starting type
      ty1 <- typeInference emptyEnv e
      -- take a step
      e' <- step e
      -- check that the expression can still be *checked* to have the same type
      let tc = checkType emptyEnv e' ty1
      runTc tc

{-
This was our first attempt at preservation. It fails for two reasons.
1) Stepping removes annotations, which can change the type (either by making it more general,
  or not being to infer the type at all since annotations provide local information)
2) Stepping an 'if' or a 'case' cane make the type more general because we might step to
  a branch with a more general type than the overall expression. For example:

    if True then \x -> x else \y -> y + 1

  This starts with type Int -> Int but steps to type forall a . a -> a
 -}
preservationBad :: Expression -> Property
preservationBad e =
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