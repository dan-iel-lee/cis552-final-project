module ParserTest where

import Control.Monad
import Parser
import Test.QuickCheck hiding (Fun)
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP
import Types

{-
==========================================================

-------------------- PARSER TESTING ----------------------

==========================================================
-}

prop_roundtrip :: Expression -> Bool
prop_roundtrip s = parse (indented s) == Just s

quickCheckN :: Test.QuickCheck.Testable prop => Int -> prop -> IO ()
quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n, maxSize = 100}

-- | Parsing uses a different Expression generator then typeinf and eval (to cover broader edge cases)
instance Arbitrary Expression where
  arbitrary = sized genExp
  shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Lam v e1) = [Lam v e1' | e1' <- shrink e1]
  shrink (App e1 e2) = [App e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Let v e1 e2) = [Let v e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink _ = []

genPattern :: Gen Pattern
genPattern =
  oneof
    [ fmap VarP arbVar,
      fmap IntP arbNat,
      fmap BoolP arbitrary
    ]

genType :: Int -> Gen Type
genType 0 = elements [IntTy, BoolTy]
genType n =
  frequency
    [(1, return IntTy), (1, return BoolTy), (2, liftM2 FunTy (genType n') (genType n'))]
  where
    n' = n `div` 4

genForCase :: Int -> Gen Expression
genForCase 0 = genExp 0
genForCase n =
  frequency
    [ (1, fmap Var arbVar),
      (1, fmap IntExp arbNat),
      (1, fmap BoolExp arbitrary),
      (7, liftM3 Op arbitrary (genOp n') (genOp n')),
      (4, liftM2 App (genAppHead n') (exprList n'))
    ]
  where
    n' = n `div` 4

genAppHead :: Int -> Gen Expression
genAppHead 0 = fmap Var arbVar
genAppHead n =
  frequency
    [ (3, fmap Var arbVar),
      (1, liftM2 Lam arbVar (genExp n'))
    ]
  where
    n' = n `div` 4

genForApp :: Int -> Gen Expression
genForApp 0 = genExp 0
genForApp n =
  frequency
    [ (1, fmap Var arbVar),
      (1, fmap IntExp arbNat),
      (1, fmap BoolExp arbitrary),
      (7, liftM3 Op arbitrary (genOp n') (genOp n')),
      (7, liftM2 Lam arbVar (genExp n')),
      (4, liftM2 App (genAppHead n') (exprList n'))
    ]
  where
    n' = n `div` 4

genOp :: Int -> Gen Expression
genOp 0 = genExp 0
genOp n =
  frequency
    [ (2, fmap Var arbVar),
      (2, fmap IntExp arbNat),
      (2, fmap BoolExp arbitrary),
      (3, liftM3 Op arbitrary (genOp n') (genOp n')),
      (4, liftM2 App (genAppHead n') (exprList n'))
    ]
  where
    n' = n `div` 4

genExp :: Int -> Gen Expression
genExp 0 =
  oneof
    [ fmap Var arbVar,
      fmap IntExp arbNat,
      fmap BoolExp arbitrary
    ]
genExp n =
  frequency
    [ (1, fmap Var arbVar),
      (1, fmap IntExp arbNat),
      (1, fmap BoolExp arbitrary),
      (7, liftM3 Op arbitrary (genOp n') (genOp n')),
      (2, liftM2 Case (genForCase n') (patternList n')),
      (7, liftM2 Lam arbVar (genExp n')),
      (4, liftM2 App (genAppHead n') (exprList n')),
      (7, liftM3 Let arbVar (genExp n') (genExp n'))
    ]
  where
    n' = n `div` 4

patternList :: Int -> Gen [(Pattern, Expression)]
patternList 0 = foldr (liftM2 (:)) (return []) (replicate 1 $ liftM2 (,) genPattern (genForCase 0))
patternList n = foldr (liftM2 (:)) (return []) (replicate n $ liftM2 (,) genPattern (genForCase n))

exprList :: Int -> Gen [Expression]
exprList 0 = foldr (liftM2 (:)) (return []) $ replicate 1 (genForApp 0)
exprList n = foldr (liftM2 (:)) (return []) $ replicate n (genForApp n)

instance Arbitrary Bop where
  arbitrary = elements [Plus ..]

arbNat :: Gen Int
arbNat = fmap abs arbitrary

arbVar :: Gen Variable
arbVar = elements $ map pure ['a' .. 'z']
