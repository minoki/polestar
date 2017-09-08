-- Read-Eval-Print loop

module Main where
import Polestar.Core.Parse
import Polestar.Core.Type
import Polestar.Core.TypeCheck
import Polestar.Core.PrettyPrint
import Polestar.Core.Eval
import Control.Monad (when)
import System.IO
import Text.Parsec
import System.Console.Haskeline -- from `haskeline' package

data ReplCommand = ReplEval Term !Bool
                 | ReplTermDef String Term

replCommand :: [NameBinding] -> Parser ReplCommand
replCommand ctx = termDef <|> termEval <?> "REPL Command"
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

data REPLBinding = Let String Term Type

toNameBinding :: REPLBinding -> NameBinding
toNameBinding (Let name _ _) = NVarBind name

toBinding :: REPLBinding -> Binding
toBinding (Let name _ ty) = VarBind (Id name) ty

toValueBinding :: REPLBinding -> ValueBinding
toValueBinding (Let _ v _) = ValueBind v

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
        Right (ReplEval tm stepByStep) -> case typeOf (map toBinding ctx) tm of
          Left error -> do
            outputStrLn $ "Type error: " ++ error
            repl ctx
          Right ty -> do
            outputStrLn $ "Type is " ++ prettyPrintType ty ++ "."
            outputStrLn "Evaluation:"
            outputStrLn (prettyPrintTerm tm)
            evalLoop tm stepByStep
            repl ctx
        Right (ReplTermDef name tm) -> case typeOf (map toBinding ctx) tm of
          Left error -> do
            outputStrLn $ "Type error: " ++ error
            repl ctx
          Right ty -> do
            outputStrLn $ name ++ " : " ++ prettyPrintType ty ++ "."
            outputStrLn "Evaluation:"
            outputStrLn (prettyPrintTerm tm)
            result <- evalLoop tm False
            case result of
              Just value -> repl (Let name value ty : ctx)
              Nothing -> repl ctx
  where
    prettyPrintType t = prettyPrintTypeP 0 (map toNameBinding ctx) t ""
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
  outputStrLn "This is Polestar.Core REPL."
  outputStrLn "Press Ctrl-D to exit."
  repl []
