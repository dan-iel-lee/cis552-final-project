module Parser where

import Control.Applicative (Alternative (..))
import Control.Monad
import qualified Data.Char as Char
import qualified ParserCombinators as P
import Test.QuickCheck hiding (Fun)
import Test.HUnit
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP
import Types

-- HELPERS
-- =====================

-- parse something then consume all following whitespace
wsP :: P.Parser a -> P.Parser a
wsP p = p <* many (P.satisfy Char.isSpace)

-- a parser that looks for a particular string, then consumes all
-- whitespace afterwards.
kwP :: String -> P.Parser String
kwP s = wsP $ P.string s

varP :: P.Parser Variable
varP = wsP (some (P.satisfy Char.isUpper))

boolP :: P.Parser Bool
boolP =
  (kwP "true" *> pure True)
    <|> (kwP "false" *> pure False)

-- only natural numbers for simplicity (no negative numbers)
intP :: P.Parser Int
intP = oneNat

oneNat :: P.Parser Int
oneNat = read <$> some (P.satisfy Char.isDigit)

-- know that read will succeed because input is all digits

char :: Char -> P.Parser Char
char c = P.satisfy (== c)

parenP :: P.Parser a -> P.Parser a
parenP p = char '(' *> p <* char ')'

-- DATATYPE PARSING
-- =====================

patternParser :: String -> P.Parser Pattern
exprParser :: String -> P.Parser Expression

-- ======================
-- DECLARATION PARSING
-- ========================

-- x = 3 => let x = 3
{-
x = 3

y = fun X -> X

y x
 -}
data Declaration = Dec Variable Expression

decParser :: String -> P.Parser Declaration
parseDec :: String -> Maybe Declaration

-- ==========================
-- EXPRESSION PARSING
-- ===========================

-- example of an expression
factExp :: Expression
factExp =
  Let
    "FACT"
    ( Lam
        "X"
        ( If
            (Op Le (Var "X") (IntExp 1))
            (IntExp 1)
            (Op Times (Var "X") (App (Var "FACT") (Op Minus (Var "X") (IntExp 1))))
        )
    )
    (App (Var "FACT") (IntExp 5))

opP :: P.Parser Bop
opP =
  (kwP "+" *> pure Plus)
    <|> (kwP "-" *> pure Minus)
    <|> (kwP "*" *> pure Times)
    <|> (kwP ">=" *> pure Ge)
    <|> (kwP "<=" *> pure Le)
    <|> (kwP ">" *> pure Gt)
    <|> (kwP "<" *> pure Lt)

varExprP = Var <$> wsP varP

boolExprP = BoolExp <$> wsP boolP

intExprP = IntExp <$> wsP intP

ifP =
  If
    <$> (kwP "if" *> exprP)
    <*> (kwP "then" *> exprP)
    <*> (kwP "else" *> exprP)

funP =
  Fun
    <$> (kwP "fun" *> varP)
    <*> (kwP "->" *> exprP)

letrecP =
  Let
    <$> (kwP "let" *> varP)
    <*> (kwP "=" *> exprP)
    <*> (kwP "in" *> exprP)

-- we use chainl1 for associativity and precedence
exprP :: P.Parser Expression
exprP = sumP
  where
    sumP = prodP `P.chainl1` (Op <$> addOp)
    prodP = compP `P.chainl1` (Op <$> mulOp)
    compP = appP `P.chainl1` (Op <$> cmpOp)
    appP = factorP `P.chainl1` wsP (pure App)
    factorP = wsP (parenP exprP) <|> baseP
    baseP =
      boolExprP <|> intExprP <|> ifP <|> funP <|> letrecP
        <|> varExprP

addOp :: P.Parser Bop
addOp =
  kwP "+" *> pure Plus
    <|> kwP "-" *> pure Minus

mulOp :: P.Parser Bop
mulOp = kwP "*" *> pure Times

cmpOp :: P.Parser Bop
cmpOp =
  kwP "<=" *> pure Le
    <|> kwP ">=" *> pure Ge
    <|> kwP "<" *> pure Lt
    <|> kwP ">" *> pure Gt

parse :: String -> Maybe Expression
parse s = fst <$> P.doParse exprP s

-- TESTING
ex1_S = "y = fun x -> x \ny 3"

ex1_E = Let "y" (Lam "x" (Var "x")) (App (Var "y") (IntExp 3))

--

-- PRETTY PRINTING
-- ======================

instance PP Bop where
  pp Plus = PP.text "+"
  pp Minus = PP.text "-"
  pp Times = PP.text "*"
  pp Gt = PP.text ">"
  pp Ge = PP.text ">="
  pp Lt = PP.text "<"
  pp Le = PP.text "<="

class PP a where
  pp :: a -> Doc

display :: PP a => a -> String
display = show . pp

instance PP Variable where
  pp s = PP.text s

instance PP Expression where
  pp (Var x) = PP.text x
  pp (IntExp x) = PP.text (show x)
  pp (BoolExp x) = if x then PP.text "true" else PP.text "false"
  pp e@(Op {}) = ppPrec 0 e
  pp (If e s1 s2) =
    PP.vcat
      [ PP.text "if" <+> pp e <+> PP.text "then",
        PP.nest 2 (pp s1),
        PP.text "else",
        PP.nest 2 (pp s2)
      ]
  pp e@(App _ _) = ppPrec 0 e
  pp (Fun x e) =
    PP.hang (PP.text "fun" <+> pp x <+> PP.text "->") 2 (pp e)
  pp (Let x e1 e2) =
    PP.vcat
      [ PP.text "let" <+> pp x <+> PP.text "=",
        PP.nest 2 (pp e1),
        PP.text "in",
        PP.nest 2 (pp e2)
      ]

ppPrec n (Op bop e1 e2) =
  parens (level bop < n) $
    ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
ppPrec n (App e1 e2) =
  parens (levelApp < n) $
    ppPrec levelApp e1 <+> ppPrec (levelApp + 1) e2
ppPrec n e@(Fun _ _) =
  parens (levelFun < n) $ pp e
ppPrec n e@(If {}) =
  parens (levelIf < n) $ pp e
ppPrec n e@(Let {}) =
  parens (levelLet < n) $ pp e
ppPrec _ e' = pp e'

parens b = if b then PP.parens else id

-- emulate the C++ precendence-level table
level :: Bop -> Int
level Plus = 3
level Minus = 3
level Times = 5
level _ = 8

levelApp = 10

levelIf = 2

levelLet = 1

levelFun = 1 -- (= almost always needs parens)

indented :: PP a => a -> String
indented = PP.render . pp

-- Declaration unit tests

decTests :: Test
decTests = TestList [
    parseDec "x = 5" ~?= Just (Var "x") (IntExp 5),
    parseDec "x = 5 + y" ~?= Just (Var "x") (Op (IntExp 5) Plus (Var "y")),
    parseDec "y = \\x -> x * 3" ~?= Just (Var "y") (Lam (Var "x") (Op (Var "x") Times (IntVar 3)))
  ]

-- Roundtrip property testing

prop_roundtrip :: Expression -> Bool
prop_roundtrip s = parse (indented s) == Just s

quickCheckN :: Test.QuickCheck.Testable prop => Int -> prop -> IO ()
quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n, maxSize = 100}

instance Arbitrary Expression where
  arbitrary = sized genExp
  shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (If e1 e2 e3) = [If e1' e2' e3' | e1' <- shrink e1, e2' <- shrink e2, e3' <- shrink e3]
  shrink (Fun v e1) = [Fun v e1' | e1' <- shrink e1]
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
genType 0 = oneof [IntTy, BoolTy]
genType n = frequency
              [ (1, IntTy), (1, BoolTy), (2, liftM2 Fun (genType n') (genType n'))]
            where n' = n `div` 2

genAppHead :: Gen AppHead
genAppHead n =
  oneof
    [ fmap Var arbVar,
      liftM2 Annot (genExp n) (genType n),
      genExp n
    ]

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
      (7, liftM3 Op arbitrary (genExp n') (genExp n')),
      (4, liftM2 Case (genExp n') (replicate n' (genPattern, genExp n'))),
      (7, liftM2 Lam arbVar (genExp n')),
      (4, liftM2 App (genAppHead n') (replicate n' (genExp n'))),
      (7, liftM3 Let arbVar (genExp n') (genExp n'))
    ]
  where
    n' = n `div` 2

instance Arbitrary Bop where
  arbitrary = elements [Plus ..]

instance Arbitrary 

arbNat :: Gen Int
arbNat = liftM abs arbitrary

arbVar :: Gen Variable
arbVar = elements $ map pure ['a' .. 'z']