{-# LANGUAGE FlexibleInstances,
             UndecidableInstances, CPP, ViewPatterns,
             NondecreasingIndentation, LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
{-# OPTIONS_GHC -fno-warn-unrecognised-pragmas #-}

#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Glee.Repl
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- Implements a REPL for Glee.
--
----------------------------------------------------------------------------

module Language.Glee.Repl  where

import Prelude hiding (lex)

import Language.Glee.Check
import Language.Glee.Eval
import Language.Glee.Lex
import Language.Glee.Parse
import Language.Glee.Unchecked
import Language.Glee.Util
import Language.Glee.Statement
import Language.Glee.Globals
import Language.Glee.Monad
import Language.Glee.Exp
import Language.Glee.Type
import Language.Glee.Hasochism 
import Text.PrettyPrint.ANSI.Leijen as Pretty hiding ( (<$>) )
import System.Directory
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as List
import Data.Text 
import System.Console.Haskeline
import Language.Glee.Ascii 
import qualified Data.Map as M
import Control.Lens (over, view, set)
import Data.Singletons
import Control.Monad.Except

class Reportable a where
  report :: a -> Glam Globals

instance {-# OVERLAPPABLE #-} Pretty a => Reportable a where
  report other = printLine (pretty other) >> get

reportErrors :: Reportable a => GlamE a -> Glam ()
reportErrors thing_inside = do
  result <- runGlamE thing_inside
  new_globals <- case result of
    Left err -> printLine err >> get
    Right x  -> report x
  put new_globals

printValWithType :: Val ty -> STy ty -> Doc
printValWithType val sty
  = prettyVal val sty <+> colon <+> pretty sty

testLex :: Text -> IO ()
testLex txt = do 
  let mytokens = lex txt 
  case mytokens of 
    Left err -> print err 
    Right toks -> print toks  

printWithType :: (Pretty exp, Pretty ty) => exp -> ty -> Doc
printWithType exp ty
  = pretty exp <+> colon <+> pretty ty

-- | The glamorous Glee interpreter
main :: IO ()
main = runInputT defaultSettings $
       runGlam $ do
         helloWorld
         loop

loop :: Glam ()
loop = do
  m_line <- prompt "λ> "
  case stripWhitespace <$> m_line of
    Nothing          -> quit
    Just (':' : cmd) -> runCommand cmd
    Just str         -> runStmts str
  loop

-- | Prints welcome message
helloWorld :: Glam ()
helloWorld = do
  printLine lambda
  printLine $ text "Welcome to the Glamorous Glee interpreter, version" <+>
              text version <> char '.'

-- | The welcome message
lambda :: Doc
lambda
  = vcat $ List.map text
    [ "         \\\\\\\\\\\\      _   _  "
    , "          \\\\\\\\\\\\    |_  |_  "
    , "       /-\\ \\\\\\\\\\\\   |_  |_ "
    , "      |   | \\\\\\\\\\\\          "
    , "       \\-/|  \\\\\\\\\\\\        "
    , "          | //\\\\\\\\\\\\        "
    , "       \\-/ ////\\\\\\\\\\\\      "
    , "          //////\\\\\\\\\\\\      "
    , "         //////  \\\\\\\\\\\\     "
    , "        //////    \\\\\\\\\\\\    "
    ]

-- | The current version of Glee
version :: String
version = "1.0"

-------------------------------------------
-- running statements

runStmts :: String -> Glam ()
runStmts str = reportErrors $ do
    toks <- lexG . pack $ str
    stmts <- parseStmtsG toks
    doStmts stmts

-- | Run a sequence of statements, returning the new global variables
doStmts :: [Statement] -> GlamE Globals
doStmts  = List.foldr doStmt ask

liftGlam :: Glam a -> GlamE a 
liftGlam m = GlamE $ lift m 

-- | Run a 'Statement' and then run another action with the global
-- variables built in the 'Statement'
doStmt :: Statement -> GlamE a -> GlamE a
doStmt (BareExp uexp) thing_inside = check uexp $ \sty exp -> do
  printLine $ printValWithType (eval exp) sty
  thing_inside
doStmt (NewGlobal g uexp) thing_inside = check uexp $ \sty exp -> do
  printLine $ text (toString g) <+> char '=' <+> printWithType exp sty
  local (extend g sty exp) thing_inside
doStmt (TyDec l t) thing_inside = do 
    updateConstructors t 
    liftGlam $ modify $ over (globalContext . types) $ M.insert l t
    thing_inside  
  where 
    updateConstructors :: Ty -> GlamE ()
    updateConstructors t' = case toSing t' of 
      SomeSing st -> case st of 
        v@(SVariantTy vs) -> case mkConstructors v of 
          Just cs -> insertConstructors cs 
          Nothing -> throwError $ text "Error: Invalid Sum Type or Constructor"

    insertConstructors :: [Some ConstructorInfo] -> GlamE ()
    insertConstructors [] = pure ()
    insertConstructors (x:xs) = case x of 
      Some c@(MkConstructor sl _ _) -> do
        Some e <- asks (view (globalContext . dataCons))
        case withSingI sl $ hInsert c e of 
          Left err -> throwError $ text err 
          Right newCons -> do 
            liftGlam $ modify $ set (globalContext . dataCons) (Some newCons)
            insertConstructors xs   
-------------------------------------------
-- commands

-- | Interpret a command (missing the initial ':').
runCommand :: String -> Glam ()
runCommand = dispatchCommand cmdTable

type CommandTable = [(String, String -> Glam ())]

dispatchCommand :: CommandTable -> String -> Glam ()
dispatchCommand table line
  = case List.filter ((cmd `List.isPrefixOf`) . fst) table of
      []            -> printLine $ text "Unknown command:" <+> squotes (text cmd)
      [(_, action)] -> action arg
      many          -> do printLine $ text "Ambiguous command:" <+> squotes (text cmd)
                          printLine $ text "Possibilities:" $$
                                      indent 2 (vcat $ List.map (text . fst) many)
  where (cmd, arg) = List.break isSpace line

cmdTable :: CommandTable
cmdTable = [ ("quit",    quitCmd)
           , ("d-lex",   lexCmd)
           , ("d-parse", parseCmd)
           , ("load",    loadCmd)
           , ("eval",    evalCmd)
           , ("type",    typeCmd) ]

quitCmd :: String -> Glam ()
quitCmd _ = quit

instance Reportable Doc where
  report x = printLine x >> get
instance Reportable () where
  report _ = get
instance Reportable Globals where
  report = return

parseLex :: String -> GlamE UExp
parseLex = (parseExpG <=< lexG) . pack  

lexCmd, parseCmd, evalCmd, typeCmd,  loadCmd
  :: String -> Glam ()
lexCmd expr = reportErrors . lexG . pack $ expr
parseCmd = reportErrors . parseLex

evalCmd expr = reportErrors $ do
  uexp <- parseLex expr
  check uexp $ \sty exp ->
    return $ printValWithType (eval exp) sty

typeCmd expr = reportErrors $ do
  uexp <- parseLex expr
  check uexp $ \sty exp -> return (printWithType exp sty)


loadCmd (stripWhitespace -> file) = do
  file_exists <- liftIO $ doesFileExist file
  if not file_exists then file_not_found else do
  contents <- liftIO $ readFile file
  runStmts contents
  where
    file_not_found = do
      printLine (text "File not found:" <+> squotes (text file))
      cwd <- liftIO getCurrentDirectory
      printLine (parens (text "Current directory:" <+> text cwd))
