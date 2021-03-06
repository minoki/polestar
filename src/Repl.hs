-- Read-Eval-Print loop

module Main where
import Polestar.Parse
import Polestar.Type
import Polestar.Subtype
import Polestar.TypeCheck
import Polestar.PrettyPrint
import Polestar.Eval (termShift,termTypeSubst,eval1,ValueBinding(..))
import Control.Monad (when)
import System.IO
import Text.Parsec
import System.Console.Haskeline -- from `haskeline' package

data ReplCommand = ReplEval Term !Bool
                 | ReplTermDef String Term
                 | ReplTypeDef String Type
                 | ReplCheckType Type
                 | ReplCheckSub Type Type
                 | ReplTypeJoin Type Type

replCommand :: [NameBinding] -> Parser ReplCommand
replCommand ctx = termDef <|> typeJoin <|> checkType <|> typeDef <|> checkSub <|>  termEval <?> "REPL Command"
  where
    termEval = do
      whiteSpace
      stepByStep <- (reserved "step" >> return True) <|> return False
      t <- term ctx
      eof
      return (ReplEval t stepByStep)
    termDef = try $ do
      reserved "let"
      name <- identifier
      reservedOp "="
      t <- term ctx
      eof
      return (ReplTermDef name t)
    typeDef = try $ do
      reserved "type"
      name <- identifier
      reservedOp "="
      t <- typeExpr ctx
      eof
      return (ReplTypeDef name t)
    checkSub = try $ do
      reserved "check"
      s <- typeExpr ctx
      reservedOp "<:"
      t <- typeExpr ctx
      eof
      return (ReplCheckSub s t)
    checkType = try $ do
      reserved "type"
      s <- typeExpr ctx
      eof
      return (ReplCheckType s)
    typeJoin = try $ do
      reserved "type"
      reserved "join"
      s <- typeExpr ctx
      reservedOp ","
      t <- typeExpr ctx
      eof
      return (ReplTypeJoin s t)

data REPLBinding = Let String Term CanonicalType
                 | TypeDef String CanonicalType

toNameBinding :: REPLBinding -> NameBinding
toNameBinding (Let name _ _) = NVarBind name
toNameBinding (TypeDef name _) = NTyVarBind name

toBinding :: REPLBinding -> Binding
toBinding (Let name _ ty) = VarBind (Id name) ty
toBinding (TypeDef name ty) = TyVarBind (Id name) []

toValueBinding :: REPLBinding -> ValueBinding
toValueBinding (Let _ v _) = ValueBind v
toValueBinding (TypeDef _ _) = TypeBind

resolveTypeAliasInTerm :: Type -> Int -> Term -> Term
resolveTypeAliasInTerm ty i = termShift 1 i . termTypeSubst ty i
resolveTypeAliasesInTerm :: [REPLBinding] -> Int -> Term -> Term
resolveTypeAliasesInTerm [] _ = id
resolveTypeAliasesInTerm (Let name m ty : xs) i = resolveTypeAliasesInTerm xs (i + 1)
resolveTypeAliasesInTerm (TypeDef name ty : xs) i = resolveTypeAliasesInTerm xs (i + 1) . resolveTypeAliasInTerm (canonicalToOrdinary ty) i

resolveTypeAliasInType :: Type -> Int -> Type -> Type
resolveTypeAliasInType ty i = typeShift 1 i . typeSubst ty i
resolveTypeAliasesInType :: [REPLBinding] -> Int -> Type -> Type
resolveTypeAliasesInType [] _ = id
resolveTypeAliasesInType (Let name m ty : xs) i = resolveTypeAliasesInType xs (i + 1)
resolveTypeAliasesInType (TypeDef name ty : xs) i = resolveTypeAliasesInType xs (i + 1) . resolveTypeAliasInType (canonicalToOrdinary ty) i

repl :: [REPLBinding] -> InputT IO ()
repl ctx = do
  mline <- getInputLine "> "
  case mline of
    Nothing -> outputStrLn "Bye!" -- EOF / Ctrl-D
    Just line -> do
      case parse (replCommand (map toNameBinding ctx)) "<stdin>" line of
        Left error -> do
          outputStrLn $ show error -- parse error
          repl ctx
        Right (ReplEval tm stepByStep) -> let tm' = resolveTypeAliasesInTerm ctx 0 tm
          in case typeOf (map toBinding ctx) tm' of
               Left error -> do
                 outputStrLn $ "Type error: " ++ error
                 repl ctx
               Right ty -> do
                 let ty' = normalizeType (map toBinding ctx) ty
                 outputStrLn $ "Type is " ++ prettyPrintCanonicalType ty' ++ "."
                 outputStrLn "Evaluation:"
                 outputStrLn (prettyPrintTerm tm')
                 evalLoop tm' stepByStep
                 repl ctx
        Right (ReplTermDef name tm) -> let tm' = resolveTypeAliasesInTerm ctx 0 tm
          in case typeOf (map toBinding ctx) tm' of
               Left error -> do
                 outputStrLn $ "Type error: " ++ error
                 repl ctx
               Right ty -> do
                 let ty' = normalizeType (map toBinding ctx) ty
                 outputStrLn $ name ++ " : " ++ prettyPrintCanonicalType ty' ++ "."
                 outputStrLn "Evaluation:"
                 outputStrLn (prettyPrintTerm tm')
                 result <- evalLoop tm' False
                 case result of
                   Just value -> repl (Let name value ty' : ctx)
                   Nothing -> repl ctx
        Right (ReplTypeDef name ty) -> do
          let ty' = normalizeType (map toBinding ctx) ty
          outputStrLn $ name ++ " := " ++ prettyPrintCanonicalType ty' ++ "."
          repl (TypeDef name ty' : ctx)
        Right (ReplCheckType ty) -> do
          let ty' = normalizeType (map toBinding ctx) ty
          outputStrLn $ prettyPrintCanonicalType ty' ++ "."
          repl ctx
        Right (ReplCheckSub s t) -> do
          let s' = normalizeType (map toBinding ctx) s
          let t' = normalizeType (map toBinding ctx) t
          if subTypeC (map toBinding ctx) s' t'
            then outputStrLn $ prettyPrintCanonicalType s' ++ " is a subtype of " ++ prettyPrintCanonicalType t' ++ "."
            else outputStrLn $ prettyPrintCanonicalType s' ++ " is not a subtype of " ++ prettyPrintCanonicalType t' ++ "."
          repl ctx
        Right (ReplTypeJoin s t) -> do
          let s' = normalizeType (map toBinding ctx) s
          let t' = normalizeType (map toBinding ctx) t
          outputStrLn $ prettyPrintCanonicalType (joinTypeC (map toBinding ctx) s' t') ++ "."
          repl ctx
  where
    prettyPrintCanonicalType t = prettyPrintCanonicalTypeP 0 (map toNameBinding ctx) t ""
    prettyPrintTerm t = prettyPrintTermP 0 (map toNameBinding ctx) t ""
    evalLoop :: Term -> Bool -> InputT IO (Maybe Term)
    evalLoop t stepByStep = case eval1 (map toValueBinding ctx) t of
      Left error -> do outputStrLn $ "Evaluation error: " ++ error
                       return Nothing
      Right t' | isValue t' -> do
                   outputStrLn $ "--> " ++ prettyPrintTerm t' ++ "."
                   return (Just t')
               | otherwise -> do
                   if stepByStep
                     then outputStrLn $ "--> " ++ prettyPrintTerm t'
                     else return ()
                   evalLoop t' stepByStep

main :: IO ()
main = runInputT defaultSettings $ do
  outputStrLn "This is Polestar REPL."
  outputStrLn "Press Ctrl-D to exit."
  repl []
