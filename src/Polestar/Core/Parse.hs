module Polestar.Core.Parse where
import Polestar.Core.Type
import Text.Parsec
import qualified Text.Parsec.Token as PT
import qualified Text.Parsec.Expr as PE
import Data.List (elemIndex)
import Data.Foldable (foldl')
import qualified Polestar.Parse.Number as NP

type Parser = Parsec String ()

data NameBinding = NVarBind String
                 | NAnonymousBind
                 | NTyVarBind String
                 deriving (Eq,Show)

builtinTypes :: [(String,Type)]
builtinTypes = [("Nat",TyNat)
               ,("Int",TyInt)
               ,("Real",TyReal)
               ,("Bool",TyBool)
               ,("Unit",TyUnit)
               ]

unaryFns :: [(String,UnaryFn)]
unaryFns = [("negateInt",UNegateInt)
           ,("negateReal",UNegateReal)
           ,("natToInt",UNatToInt)
           ,("intToReal",UIntToReal)
           ,("intToNat",UIntToNat)
           ]

binaryFns :: [(String,BinaryFn)]
binaryFns = [("addNat",UAddNat)
            ,("mulNat",UMulNat)
            ,("truncSubNat",UTSubNat)
            ,("powNat",UPowNatNat)
            ,("equalNat",UEqualNat)
            ,("lessThanNat",ULessThanNat)
            ,("lessEqualNat",ULessEqualNat)
            ,("addInt",UAddInt)
            ,("subInt",USubInt)
            ,("mulInt",UMulInt)
            ,("powInt",UPowIntNat)
            ,("equalInt",UEqualInt)
            ,("lessThanInt",ULessThanInt)
            ,("lessEqualInt",ULessEqualInt)
            ,("addReal",UAddReal)
            ,("subReal",USubReal)
            ,("mulReal",UMulReal)
            ,("powReal",UPowRealReal)
            ,("equalReal",UEqualReal)
            ,("lessThanReal",ULessThanReal)
            ,("lessEqualReal",ULessEqualReal)
            ]

builtins :: [(String,PrimValue)]
builtins = map (fmap PVUnary) unaryFns ++ map (fmap PVBinary) binaryFns

langDef = PT.LanguageDef { PT.commentStart = ""
                         , PT.commentEnd = ""
                         , PT.commentLine = ""
                         , PT.nestedComments = False
                         , PT.identStart = letter <|> char '_'
                         , PT.identLetter = alphaNum <|> char '_'
                         , PT.opStart = oneOf ":!#$&*+./<=>?@\\^|-~"
                         , PT.opLetter = oneOf ":!#$&*+./<=>?@\\^|-~"
                         , PT.reservedNames = ["if","then","else","true","false","forall","as","let","in","for","default","type","unit","_"] ++ map fst builtins ++ map fst builtinTypes
                         , PT.reservedOpNames = ["->","<:","\\",".","&","?",":","=","@"]
                         , PT.caseSensitive = True
                         }
tokenParser = PT.makeTokenParser langDef
lexeme = PT.lexeme tokenParser
identifier = PT.identifier tokenParser :: Parser String
reserved = PT.reserved tokenParser :: String -> Parser ()
operator = PT.operator tokenParser :: Parser String
reservedOp = PT.reservedOp tokenParser :: String -> Parser ()
symbol = PT.symbol tokenParser :: String -> Parser String
parens = PT.parens tokenParser
braces = PT.braces tokenParser
brackets = PT.brackets tokenParser
whiteSpace = PT.whiteSpace tokenParser
natural = PT.natural tokenParser

simpleTypeExpr :: [NameBinding] -> Parser Type
simpleTypeExpr ctx = choice [reserved name >> return t | (name,t) <- builtinTypes]
                     <|> parens (do types <- sepBy1 (typeExpr ctx) (reservedOp ",")
                                    case types of
                                      [] -> error "sepBy1 returned an empty list"
                                      [t] -> return t
                                      types -> return $ TyTuple types)
                     <?> "simple type expression"

arrTypeExpr :: [NameBinding] -> Parser Type
arrTypeExpr ctx = do a <- simpleTypeExpr ctx
                     ((reservedOp "->" >> (TyArr a <$> arrTypeExpr (NAnonymousBind : ctx)))
                       <|> return a)
                  <?> "type expression"

typeExpr :: [NameBinding] -> Parser Type
typeExpr ctx = arrTypeExpr ctx
                 <?> "type expression"

simpleTerm :: [NameBinding] -> Parser Term
simpleTerm ctx = (reserved "true" >> return (TmPrim $ PVBool True))
                 <|> (reserved "false" >> return (TmPrim $ PVBool False))
                 <|> (reserved "unit" >> return (TmPrim PVUnit))
                 <|> lexeme (do x <- NP.natFloat <?> "number"
                                TmPrim <$> case x of
                                  Left n -> do
                                    suffix <- (char '%' >> oneOf "NZR") <|> return 'Z'
                                    case suffix of
                                      'R' -> return (PVReal $ fromInteger n)
                                      'Z' -> return (PVInt n)
                                      _ -> return (PVNat n)
                                  Right x -> return (PVReal x))
                 <|> parens (do components <- sepBy1 (term ctx) (reservedOp ",")
                                case components of
                                  [] -> error "sepBy1 returned an empty list"
                                  [t] -> return t
                                  components -> return $ TmTuple components)
                 <|> choice [reserved name >> return (TmPrim v) | (name,v) <- builtins]
                 <|> (do name <- identifier <?> "variable"
                         case NVarBind name `elemIndex` ctx of
                           Just i -> return (TmRef i)
                           Nothing -> fail ("undefined variable: " ++ name))
                 <?> "simple expression"

-- function application / type application / type coercion / projection
appTerm :: [NameBinding] -> Parser Term
appTerm ctx = iterateTerm <|> do
  x <- simpleTerm ctx
  xs <- many ((flip TmApp <$> simpleTerm ctx)
               <|> (flip TmProj <$> (char '@' >> (fromInteger <$> natural))))
  return (foldl' (flip ($)) x xs)
  where
    iterateTerm = do
      reserved "iterate"
      n <- simpleTerm ctx
      init <- simpleTerm ctx
      succ <- simpleTerm ctx
      return (TmIterate n init succ)

term :: [NameBinding] -> Parser Term
term ctx = lambdaAbstraction
           <|> letIn
           <|> ifThenElse
           <|> appTerm ctx
           <?> "expression"
  where lambdaAbstraction = do
          reservedOp "\\"
          name <- identifier
          reservedOp ":"
          varType <- typeExpr ctx
          reservedOp "."
          body <- term (NVarBind name : ctx)
          return (TmAbs (Id name) varType body)
        letIn = do
          reserved "let"
          name <- identifier
          reservedOp "="
          definition <- term ctx
          reserved "in"
          body <- term (NVarBind name : ctx)
          return $ TmLet (Id name) definition body
        ifThenElse = do
          reserved "if"
          cond <- term ctx
          reserved "then"
          thenExpr <- term ctx
          reserved "else"
          elseExpr <- term ctx
          return (TmIf cond thenExpr elseExpr)

parseType :: SourceName -> String -> Either ParseError Type
parseType name input = parse wholeParser name input
  where wholeParser = do
          whiteSpace
          t <- typeExpr []
          eof
          return t

parseTerm :: SourceName -> String -> Either ParseError Term
parseTerm name input = parse wholeParser name input
  where wholeParser = do
          whiteSpace
          t <- term []
          eof
          return t
