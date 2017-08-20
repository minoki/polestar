module Polestar.Parse where
import Polestar.Type
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
builtinTypes = [("Zero",TyZero)
               ,("Nat",TyNat)
               ,("Int",TyInt)
               ,("NNReal",TyNNReal)
               ,("Real",TyReal)
               ,("Imaginary",TyImaginary)
               ,("Complex",TyComplex)
               ,("True",TyTrue)
               ,("False",TyFalse)
               ,("Bool",TyBool)
               ,("Unit",TyUnit)
               ]

builtins :: [(String,PrimValue)]
builtins = map (fmap PVBuiltin)
           [("negate",BNegate)
           ,("not",BLogicalNot)
           ,("natToInt",BNatToInt)
           ,("natToNNReal",BNatToNNReal)
           ,("intToNat",BIntToNat)
           ,("intToReal",BIntToReal)
           ,("nnrealToReal",BNNRealToReal)
           ,("realToComplex",BRealToComplex)
           ,("mkImaginary",BMkImaginary)
           ,("imaginaryToComplex",BImaginaryToComplex)
           ,("realPart",BRealPart)
           ,("imagPart",BImagPart)
           ,("abs",BAbs)
           ,("sqrt",BSqrt)
           ,("add",BAdd)
           ,("sub",BSub)
           ,("mul",BMul)
           ,("div",BDiv)
           ,("pow",BPow)
           ,("tSub",BTSubNat)
           ,("lt",BLt)
           ,("le",BLe)
           ,("equal",BEqual)
           ,("and",BLogicalAnd)
           ,("or",BLogicalOr)
           ,("iterate",BIterate)
           ]

langDef = PT.LanguageDef { PT.commentStart = ""
                         , PT.commentEnd = ""
                         , PT.commentLine = ""
                         , PT.nestedComments = False
                         , PT.identStart = letter <|> char '_'
                         , PT.identLetter = alphaNum <|> char '_'
                         , PT.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
                         , PT.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
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
                     <|> (do name <- identifier <?> "type variable"
                             case NTyVarBind name `elemIndex` ctx of
                               Just i -> return (TyRef i)
                               Nothing -> fail ("undefined type variable: " ++ name))
                     <?> "simple type expression"

arrTypeExpr :: [NameBinding] -> Parser Type
arrTypeExpr ctx = do a <- simpleTypeExpr ctx
                     ((reservedOp "->" >> (TyArr a <$> arrTypeExpr (NAnonymousBind : ctx)))
                       <|> return a)
                  <?> "type expression"

interTypeExpr :: [NameBinding] -> Parser Type
interTypeExpr ctx = do x <- arrTypeExpr ctx
                       xs <- many (reservedOp "&" >> arrTypeExpr ctx)
                       return $ case xs of
                         [] -> x
                         _ -> TyInter (x:xs)
                    <?> "type expression"

forallExpr :: [NameBinding] -> Parser Type
forallExpr ctx = do
  reserved "forall"
  name <- identifier <?> "type variable"
  bound <- (Just <$> (reservedOp "<:" >> interTypeExpr ctx)) <|> return Nothing
  reservedOp "."
  t <- typeExpr (NTyVarBind name : ctx) -- ???
  return (TyAll (Id name) bound t)

typeExpr :: [NameBinding] -> Parser Type
typeExpr ctx = forallExpr ctx <|> interTypeExpr ctx
                 <?> "type expression"

simpleTerm :: [NameBinding] -> Parser Term
simpleTerm ctx = (reserved "true" >> return (TmPrim $ PVBool True))
                 <|> (reserved "false" >> return (TmPrim $ PVBool False))
                 <|> (reserved "unit" >> return (TmPrim PVUnit))
                 <|> lexeme (do x <- NP.natFloat <?> "number"
                                let rv = case x of
                                      Left n -> fromInteger n
                                      Right x -> x
                                    rt = case x of
                                      Left 0 -> PVZero
                                      Left n -> PVInt n
                                      Right x -> PVReal x
                                (oneOf "iI" >> return (TmPrim $ PVImaginary rv)) <|> return (TmPrim rt))
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
appTerm ctx = do x <- simpleTerm ctx
                 xs <- many ((flip TmApp <$> simpleTerm ctx)
                              <|> (flip TmTyApp <$> brackets (typeExpr ctx))
                              <|> (flip TmCoerce <$> (reserved "as" >> arrTypeExpr ctx))
                              <|> (flip TmProj <$> (char '@' >> (fromInteger <$> natural))))
                 return (foldl' (flip ($)) x xs)

opTerm :: [NameBinding] -> Parser Term
opTerm ctx = PE.buildExpressionParser table (appTerm ctx) <?> "expression"
  where
    -- [postfixOp "!" -- factorial
    -- ,postfixOp "!!" -- double factorial
    -- ],
    table = [[binaryOp "^" BPow PE.AssocRight
             ]
            ,[prefixOp "-" BNegate
             ,prefixOp "¬" BLogicalNot -- \neg, \lnot
             ]
            ,[binaryOp "*" BMul PE.AssocLeft
             ,binaryOp "/" BDiv PE.AssocLeft
             ]
            ,[binaryOp "+" BAdd PE.AssocLeft
             ,binaryOp "-" BSub PE.AssocLeft
             ,binaryOp ".-" BTSubNat PE.AssocLeft -- .- or '- or -. or -' or `-
             ,binaryOp "∸" BTSubNat PE.AssocLeft
             ]
            ,[binaryOp "==" BEqual PE.AssocNone
              -- ,binaryOp "/=" BNotEqual PE.AssocNone
             ,binaryOp "<"  BLt PE.AssocNone
             ,binaryOp "<=" BLe PE.AssocNone
               -- ,binaryOp ">"  BGt PE.AssocNone
               -- ,binaryOp ">=" BGe PE.AssocNone
             ]
            ,[binaryOp "&&" BLogicalAnd PE.AssocLeft
             ]
            ,[binaryOp "||" BLogicalOr PE.AssocLeft
             ]
            ]
    prefixOp name fn = PE.Prefix (reservedOp name >> return (TmApp (TmPrim (PVBuiltin fn))))
    postfixOp name fn = PE.Postfix (reservedOp name >> return (TmApp (TmPrim (PVBuiltin fn))))
    binaryOp name fn assoc = PE.Infix (reservedOp name >> return (\x y -> TmApp (TmApp (TmPrim (PVBuiltin fn)) x) y)) assoc

term :: [NameBinding] -> Parser Term
term ctx = lambdaAbstraction
           <|> typeAbstraction
           <|> letIn
           <|> ifThenElse
           <|> typeFor
           <|> opTerm ctx
           <?> "expression"
  where lambdaAbstraction = do
          reservedOp "\\"
          name <- identifier
          reservedOp ":"
          candidates <- sepBy1 (typeExpr ctx) (reservedOp ",")
          reservedOp "."
          case candidates of
            [] -> parserZero -- impossible
            [varType] -> do
              body <- term (NVarBind name : ctx)
              return (TmAbs (Id name) varType body)
            candidates -> do
              body <- term (NVarBind name : NAnonymousBind : ctx)
              return (TmAlt (Id "_") candidates $ TmAbs (Id name) (TyRef 0) body)
        typeAbstraction = do
          reservedOp "?"
          name <- identifier
          bound <- (Just <$> (reservedOp "<:" >> interTypeExpr ctx)) <|> return Nothing
          reservedOp "."
          body <- term (NTyVarBind name : ctx)
          return (TmTyAbs (Id name) bound body)
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
        typeFor = do
          reserved "for"
          name <- identifier
          reserved "in"
          candidates <- sepBy1 (typeExpr ctx) (reservedOp ",")
          reservedOp "."
          body <- term (NTyVarBind name : ctx)
          return $ TmAlt (Id name) candidates body

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
