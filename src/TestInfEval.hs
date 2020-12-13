module TestInfEval where

import Control.Monad.Except
import Control.Monad.Fix
import Data.Either (isRight)
import Data.Map as Map
import Data.Vec.Lazy (Vec (VNil))
import Eval2
import Parser
import Test.HUnit
import Test.QuickCheck
  ( Args (maxSize, maxSuccess),
    Property,
    Testable,
    quickCheckWith,
    stdArgs,
    (==>),
  )
import TypeInf
import Types

{-
===================================================
                    Tests
===================================================
-}

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
