{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Parser where

import Control.Applicative (Alternative (..))
import Control.Monad
import Control.Monad.State (StateT, lift)
import qualified Data.Char as Char
import Data.Functor (($>))
import Data.List (genericLength)
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vec.Lazy (Vec (VNil, (:::)))
import qualified Data.Vec.Lazy as Vec
import qualified ParserCombinators as P
import Test.HUnit
import Test.QuickCheck hiding (Fun)
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP
import Types

-- TYPES
-- =====================

-- hidden arity type constructor
data HTypeConstructor = forall k. HTC (TypeConstructor k)

deriving instance Show HTypeConstructor

data HTCAndTVars = forall k. HH (TypeConstructor k, Vec k TypeVariable)

type PMonad a = StateT ([DataConstructor], [HTypeConstructor]) P.Parser a

-- HELPERS
-- =====================

-- parse something then consume all following whitespace
wsP :: P.Parser a -> P.Parser a
wsP p = p <* many (P.satisfy Char.isSpace)

wsPStrict :: P.Parser a -> P.Parser a
wsPStrict p = p <* some (P.satisfy Char.isSpace)

-- a parser that looks for a particular string, then consumes all
-- whitespace afterwards.
kwP :: String -> P.Parser String
kwP s = wsP $ P.string s

isLowerOrSpace :: Char -> Bool
isLowerOrSpace c = Char.isLower c || Char.isSeparator c

trim :: String -> String
trim = List.dropWhileEnd Char.isSeparator

varSpaceP :: P.Parser String
varSpaceP = P.P $ \s -> do
  (s', tl) <- P.doParse (some (P.satisfy isLowerOrSpace)) s
  return (trim s', tl)

constDataNameP :: P.Parser String
constDataNameP = wsP $ (++) <$> ((++) <$> some (P.satisfy Char.isUpper) <*> many (P.satisfy Char.isAlpha)) <*> varSpaceP

-- data constructors should be uppercase
constDataTypeNameP :: P.Parser String
constDataTypeNameP = wsP $ (++) <$> some (P.satisfy Char.isUpper) <*> many (P.satisfy Char.isAlpha)

-- typeP :: P.Parser String
-- typeP = wsP $ varP <|> parenP constDataNameP

-- TYPE PARSING // TODO !!!!
-- ========
-- take a type and set of variables IN SCOPE and parse the type
-- // NOTE: what might be hard
-- - Forall case (need to add to the set)
-- takes a list of allowed type variables
typeauxP :: Set TypeVariable -> P.Parser Type
typeauxP s = wsP $ intTyP <|> boolTyP <|> varTyP <|> forallP s <|> tyCstrP s
  where
    intTyP :: P.Parser Type
    intTyP = P.string "Int" $> IntTy

    boolTyP :: P.Parser Type
    boolTyP = P.string "Bool" $> BoolTy

    varTyP :: P.Parser Type
    varTyP = VarTy <$> P.satisfy (`Set.member` s)

    forallP :: Set TypeVariable -> P.Parser Type
    forallP s = do
      vars <- kwP "forall" *> tyVarsP <* P.char '.'
      let newS = s `Set.union` Set.fromList vars
      typeP newS

    tyCstrP :: Set TypeVariable -> P.Parser Type
    tyCstrP s = do
      name <- wsP upperCaseString
      tys <- many (typeP s)
      return (TyCstrS name tys)

tyVarsP :: P.Parser [TypeVariable]
tyVarsP = many (wsPStrict (P.satisfy Char.isLower))

-- tyCstrP :: Set

-- parse a "->" operator
funP :: P.Parser (Type -> Type -> Type)
funP = wsP $ P.string "->" $> FunTy

typeP :: Set TypeVariable -> P.Parser Type
typeP s = typeauxP s `P.chainr1` funP

-- variables should be lower case
varP :: P.Parser Variable
varP = wsP ((:) <$> P.satisfy Char.isLower <*> many (P.satisfy Char.isAlpha))

boolP :: P.Parser Bool
boolP =
  (kwP "True" *> pure True)
    <|> (kwP "False" *> pure False)

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

-- ======================
-- CONSTRUCTOR PARSING
-- ======================

upperCaseString :: P.Parser String
upperCaseString = (:) <$> P.satisfy Char.isUpper <*> many (P.satisfy Char.isAlpha)

-- type constructor parser
tcP :: P.Parser HTCAndTVars
tcP = do
  tcName <- wsP $ kwP "data" *> upperCaseString
  vars <- wsP $ many (wsP $ P.satisfy Char.isLower)
  return (makeTC tcName vars)

-- return (makeHTC tcName (len vars), vars)

makeTC :: String -> [TypeVariable] -> HTCAndTVars
makeTC name [] = HH (TC name SZ, VNil)
makeTC name (v : vs) =
  case makeTC name vs of
    HH (TC _ sar, vec) -> HH (TC name (SS sar), v ::: vec)

dcP :: (TypeConstructor k, Vec k TypeVariable) -> P.Parser DataConstructor
dcP (tc, vars) = do
  -- parse data constructor name
  name <- wsP upperCaseString
  -- parse argument types
  dcs <- many (typeP (foldableToSet vars))
  let retTy = TyCstr tc (fmap VarTy vars)
      -- convert to function
      funTy = typesToFunTy (NE.reverse $ retTy :| reverse dcs)
      -- add universal quantification
      dcTy = if null vars then funTy else Forall (Vec.toList vars) funTy
  return (DC name dcTy)

-- | Data constructor parser
dcsP :: (TypeConstructor k, Vec k TypeVariable) -> P.Parser [DataConstructor]
dcsP tcv = wsP (dcP tcv) `P.sepBy` wsP (P.char '|')

constP :: P.Parser (HTypeConstructor, [DataConstructor])
constP = do
  HH tcStuff@(tc, _) <- tcP
  wsP $ P.char '='
  dcs <- dcsP tcStuff
  return (HTC tc, dcs)

{-
data List a = Nil | exists b. Cons b (List a)

Cons : forall a. b -> List a -> List a
 -}
constructorsP :: P.Parser ([HTypeConstructor], [DataConstructor])
constructorsP = do
  dcss <- many constP
  return $ foldr (\(h, ds) (hs, dss) -> (h : hs, ds ++ dss)) ([], []) dcss

-- ======================
-- EXPRESSION PARSING
-- ======================

opP :: P.Parser Bop
opP =
  (kwP "+" *> pure Plus)
    <|> (kwP "-" *> pure Minus)
    <|> (kwP "*" *> pure Times)
    <|> (kwP ">=" *> pure Ge)
    <|> (kwP "<=" *> pure Le)
    <|> (kwP ">" *> pure Gt)
    <|> (kwP "<" *> pure Lt)

varExprP :: P.Parser Expression
varExprP = Var <$> wsP varP

boolExprP :: P.Parser Expression
boolExprP = BoolExp <$> wsP boolP

intExprP :: P.Parser Expression
intExprP = IntExp <$> wsP intP

ifP :: P.Parser Expression
ifP =
  If
    <$> (kwP "if" *> exprP)
    <*> (kwP "then" *> exprP)
    <*> (kwP "else" *> exprP)

lamP :: P.Parser Expression
lamP =
  Lam
    <$> (kwP "\\" *> varP)
    <*> (kwP "->" *> exprP)

letrecP :: P.Parser Expression
letrecP =
  Let
    <$> (kwP "let" *> varP)
    <*> (kwP "=" *> exprP)
    <*> (kwP "in" *> exprP)

appP :: P.Parser Expression
appP = do
  h <- exprP
  wsP $ P.char '.'
  es <- some exprP
  return $ App h es

varPP :: P.Parser Pattern
varPP = VarP <$> wsP varP

intPP :: P.Parser Pattern
intPP = IntP <$> wsP intP

boolPP :: P.Parser Pattern
boolPP = BoolP <$> wsP boolP

dataP :: P.Parser Pattern
dataP = PS <$> wsP upperCaseString <*> many patternP

patternP :: P.Parser Pattern
patternP = dataP <|> varPP <|> intPP <|> boolPP

caseP :: P.Parser Expression
caseP =
  Case
    <$> (kwP "case" *> wsP exprP)
    <*> some ((,) <$> (wsP (P.char '|') *> wsP patternP) <*> (kwP "->" *> wsP exprP))
    <* wsP (P.char ';') -- // TODO: any alternative?

dcEP :: P.Parser Expression
dcEP = CS <$> upperCaseString

exCase =
  "case n \
  \ | Z -> Z \
  \ | S m -> m ;"

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

exprP :: P.Parser Expression
exprP = wsP appPP
  where
    -- exprP = sumP

    appPP = (App <$> wsP sumP <*> some exprP) <|> sumP
    sumP = prodP `P.chainl1` (Op <$> addOp)
    prodP = compP `P.chainl1` (Op <$> mulOp)
    compP = factorP `P.chainl1` (Op <$> cmpOp)
    factorP = wsP (parenP exprP) <|> baseP
    baseP =
      {-appP <|> -} boolExprP <|> intExprP <|> ifP <|> lamP <|> letrecP
        <|> caseP
        <|> dcEP
        <|> varExprP

-- ======================
-- DECLARATION PARSING
-- ========================

data Declaration = Dec Variable Expression deriving (Show)

tempAnnotParser :: P.Parser (Variable, Type)
tempAnnotParser = P.P $ \s -> do
  (varName, s') <- P.doParse varP s
  (_, s'') <- P.doParse (kwP "::") s'
  (types, s''') <- P.doParse (typeP (Set.empty :: Set.Set TypeVariable)) s''
  return ((varName, types), s''')

decParser :: P.Parser Declaration
decParser = P.P $ \s -> do
  ((vname, types), s') <- P.doParse tempAnnotParser s
  (vname', s'') <- P.doParse (varP <* kwP "=") s'
  guard $ vname == vname'
  (expr, s''') <- P.doParse exprP s''
  return (Dec vname (Annot expr types), s''')

exDec =
  "pred :: Nat -> Nat \
  \ pred = \\n -> case n\
  \ | Z -> Z \
  \ | S m -> m ;"

-- ==============
-- Putting stuff together
-- ================

bigParser :: P.Parser Expression
bigParser = do
  (tcs, dcs) <- constructorsP
  decs <- many decParser
  expr <- exprP
  let letified = letify decs expr
      -- // TODO: first constructify the DCs
      mtcs = mapifyH tcs
      dcs' =
        mapM
          ( \(DC n ty) -> do
              ty' <- constructifyA mtcs ty
              return (DC n ty')
          )
          dcs
      constructed = do
        dcs'' <- dcs'
        constructify (mapifyH tcs) (mapifyDC dcs'') letified
  case constructed of
    Just c -> return c
    _ -> empty

letify :: [Declaration] -> Expression -> Expression
letify [] e = e
letify ((Dec v exp) : ds) e =
  let res = letify ds e
   in Let v exp res

mapifyDC :: [DataConstructor] -> Map String DataConstructor
mapifyDC = foldr (\dc@(DC name _) acc -> Map.insert name dc acc) Map.empty

mapifyH :: [HTypeConstructor] -> Map String HTypeConstructor
mapifyH = foldr (\ht@(HTC (TC name _)) acc -> Map.insert name ht acc) Map.empty

constructify :: Map String HTypeConstructor -> Map String DataConstructor -> Expression -> Maybe Expression
constructify mh md (Case e bs) = do
  e' <- constructify mh md e
  bs' <-
    mapM
      ( \(p, exp) -> do
          p' <- constructifyP md p
          return (p', exp)
      )
      bs
  return (Case e' bs')
constructify mh md (Annot e ty) = do
  e' <- constructify mh md e
  ty' <- constructifyA mh ty
  return (Annot e' ty')
constructify mh md (Lam v e) = do
  e' <- constructify mh md e
  return (Lam v e')
constructify mh md (App e es) = do
  e' <- constructify mh md e
  es' <- mapM (constructify mh md) es
  return (App e' es')
constructify mh md (Let v e1 e2) = do
  e1' <- constructify mh md e1
  e2' <- constructify mh md e2
  return (Let v e1' e2')
constructify mh md (If e1 e2 e3) = do
  e1' <- constructify mh md e1
  e2' <- constructify mh md e2
  e3' <- constructify mh md e3
  return (If e1' e2' e3')
constructify mh md (Op b e1 e2) = do
  e1' <- constructify mh md e1
  e2' <- constructify mh md e2
  return (Op b e1' e2')
constructify _ md (CS str) = C <$> Map.lookup str md
constructify _ _ e = return e

constructifyP :: Map String DataConstructor -> Pattern -> Maybe Pattern
constructifyP m (PS name ps) = do
  dc <- Map.lookup name m
  ps' <- mapM (constructifyP m) ps
  return (P dc ps')
constructifyP m (P dc ps) = do
  ps' <- mapM (constructifyP m) ps
  return (P dc ps')
constructifyP _ p = return p

constructifyA :: Map String HTypeConstructor -> Type -> Maybe Type
constructifyA m (TyCstrS name ts) = do
  (HTC tc) <- Map.lookup name m
  ts' <- mapM (constructifyA m) ts
  constAux tc ts'
  where
    constAux :: TypeConstructor k -> [Type] -> Maybe Type
    constAux tc@(TC _ SZ) [] = return $ TyCstr tc VNil
    constAux (TC name' (SS k)) (t : ts) = do
      resTy <- constAux (TC name' k) ts
      case resTy of
        TyCstr (TC _ k') vec -> return $ TyCstr (TC name (SS k')) (t ::: vec)
        _ -> Nothing
    constAux _ _ = Nothing
constructifyA m (FunTy ty1 ty2) = do
  ty1' <- constructifyA m ty1
  ty2' <- constructifyA m ty2
  return (FunTy ty1' ty2')
constructifyA m (Forall vs ty) = do
  ty' <- constructifyA m ty
  return (Forall vs ty')
constructifyA m (TyCstr tc tys) = do
  tys' <- mapM (constructifyA m) tys
  return (TyCstr tc tys')
constructifyA _ ty = return ty

parseFile :: String -> IO ()
parseFile path = do
  s <- readFile path
  print (P.doParse bigParser s)
  return ()

parseStr :: String -> IO ()
parseStr str = print (P.doParse bigParser str)

exStr :: String
exStr =
  "data Nat = Z | S Nat\
  \ pred :: Nat -> Nat \
  \ pred = \\n -> case n\
  \ | Z -> Z \
  \ | S m -> m ; \
  \ pred (S (S Z))"

-- -- TESTING
-- ex1_S = "y = fun x -> x \ny 3"

-- ex1_E = Let "y" (Lam "x" (Var "x")) (App (Var "y") (IntExp 3))

-- --

-- -- PRETTY PRINTING
-- -- ======================

-- instance PP Bop where
--   pp Plus = PP.text "+"
--   pp Minus = PP.text "-"
--   pp Times = PP.text "*"
--   pp Gt = PP.text ">"
--   pp Ge = PP.text ">="
--   pp Lt = PP.text "<"
--   pp Le = PP.text "<="

-- class PP a where
--   pp :: a -> Doc

-- display :: PP a => a -> String
-- display = show . pp

-- instance PP Variable where
--   pp s = PP.text s

-- instance PP Expression where
--   pp (Var x) = PP.text x
--   pp (IntExp x) = PP.text (show x)
--   pp (BoolExp x) = if x then PP.text "true" else PP.text "false"
--   pp e@(Op {}) = ppPrec 0 e
--   -- pp (Case e s1 s2) =
--   --   PP.vcat
--   --     [ PP.text "if" <+> pp e <+> PP.text "then",
--   --       PP.nest 2 (pp s1),
--   --       PP.text "else",
--   --       PP.nest 2 (pp s2)
--   --     ]
--   pp e@(App _ _) = ppPrec 0 e
--   pp (Lam x e) =
--     PP.hang (PP.text "\\" <+> pp x <+> PP.text "->") 2 (pp e)
--   pp (Let x e1 e2) =
--     PP.vcat
--       [ PP.text "let" <+> pp x <+> PP.text "=",
--         PP.nest 2 (pp e1),
--         PP.text "in",
--         PP.nest 2 (pp e2)
--       ]

-- ppPrec n (Op bop e1 e2) =
--   parens (level bop < n) $
--     ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
-- ppPrec n (App e1 e2) =
--   parens (levelApp < n) $
--     ppPrec levelApp e1 <+> ppPrec (levelApp + 1) e2
-- ppPrec n e@(Lam _ _) =
--   parens (levelFun < n) $ pp e
-- ppPrec n e@(Case {}) =
--   parens (levelCase < n) $ pp e
-- ppPrec n e@(Let {}) =
--   parens (levelLet < n) $ pp e
-- ppPrec _ e' = pp e'

-- parens b = if b then PP.parens else id

-- -- emulate the C++ precendence-level table
-- level :: Bop -> Int
-- level Plus = 3
-- level Minus = 3
-- level Times = 5
-- level _ = 8

-- levelApp = 10

-- levelCase = 2

-- levelLet = 1

-- levelFun = 1 -- (= almost always needs parens)

-- indented :: PP a => a -> String
-- indented = PP.render . pp

-- -- Declaration unit tests

-- decTests :: Test
-- decTests = TestList [
--     parseDec "x = 5" ~?= Just (Var "x") (IntExp 5),
--     parseDec "x = 5 + y" ~?= Just (Var "x") (Op (IntExp 5) Plus (Var "y")),
--     parseDec "y = \\x -> x * 3" ~?= Just (Var "y") (Lam (Var "x") (Op (Var "x") Times (IntVar 3)))
--   ]

-- -- Roundtrip property testing

-- prop_roundtrip :: Expression -> Bool
-- prop_roundtrip s = parse (indented s) == Just s

-- quickCheckN :: Test.QuickCheck.Testable prop => Int -> prop -> IO ()
-- quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n, maxSize = 100}

-- instance Arbitrary Expression where
--   arbitrary = sized genExp
--   shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
--   -- shrink (Case e1 e2 e3) = [If e1' e2' e3' | e1' <- shrink e1, e2' <- shrink e2, e3' <- shrink e3]
--   shrink (Lam v e1) = [Lam v e1' | e1' <- shrink e1]
--   shrink (App e1 e2) = [App e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
--   shrink (Let v e1 e2) = [Let v e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
--   shrink _ = []

-- genPattern :: Gen Pattern
-- genPattern =
--   oneof
--     [ fmap VarP arbVar,
--       fmap IntP arbNat,
--       fmap BoolP arbitrary
--     ]

-- genType :: Int -> Gen Type
-- genType 0 = oneof [IntTy, BoolTy]
-- genType n = frequency
--               [ (1, IntTy), (1, BoolTy), (2, liftM2 Fun (genType n') (genType n'))]
--             where n' = n `div` 2

-- genExp :: Int -> Gen Expression
-- genExp 0 =
--   oneof
--     [ fmap Var arbVar,
--       fmap IntExp arbNat,
--       fmap BoolExp arbitrary
--     ]
-- genExp n =
--   frequency
--     [ (1, fmap Var arbVar),
--       (1, fmap IntExp arbNat),
--       (1, fmap BoolExp arbitrary),
--       (7, liftM3 Op arbitrary (genExp n') (genExp n')),
--       (4, liftM2 Case (genExp n') (replicate n' (genPattern, genExp n'))),
--       (7, liftM2 Lam arbVar (genExp n')),
--       (4, liftM2 App (genExp n') (replicate n' (genExp n'))),
--       (7, liftM3 Let arbVar (genExp n') (genExp n'))
--     ]
--   where
--     n' = n `div` 2

-- instance Arbitrary Bop where
--   arbitrary = elements [Plus ..]

-- arbNat :: Gen Int
-- arbNat = liftM abs arbitrary

-- arbVar :: Gen Variable
-- arbVar = elements $ map pure ['a' .. 'z']