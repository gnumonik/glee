{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Language.Glee.Lex {-- ( lexG, lex ) --} where

import Prelude hiding ( lex )

import Language.Glee.Token
import Language.Glee.Monad
import Language.Glee.Util
import Language.Glee.Nat 


import Text.Megaparsec hiding (Token)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L



import Data.Maybe

--import Control.Applicative
import Control.Arrow as Arrow
import Data.Void
import Data.Text (pack, unpack,Text)
import Language.Glee.Ascii
import Data.Char (isUpper)
import qualified Text.PrettyPrint.ANSI.Leijen as PP 
import Control.Monad (void)

type Lexer = Parsec Void Text 

---------------------------------------------------
-- Utility
string_ :: Text -> Lexer ()
string_ = ignore . string

textToGlamE :: Either Text a -> GlamE a 
textToGlamE = \case 
  Left err -> issueError . PP.text . unpack $ err 
  Right x  -> pure x 

---------------------------------------------------
-- | Lex some program text into a list of 'LToken's, aborting upon failure
lexG :: Text -> GlamE [LToken]
lexG = textToGlamE . lex

-- | Lex some program text into a list of 'LToken's
lex :: Text -> Either Text [LToken]
lex = Arrow.left (pack . show) . parse lexer ""

lexeme = L.lexeme $ L.space (void $ oneOf (" \t" :: [Char])) line_comment empty 

lexer :: Lexer [LToken]
lexer = many (lexeme lexer1) <* eof 


{-- megaparsec conversion broke the whitespace or comment lexer, fix later 

-- | Overall lexer
lexer :: Lexer [LToken]
lexer = (catMaybes <$> many lexer1_ws) <* eof
--}
-- | Lex either one token or some whitespace
lexer1_ws :: Lexer (Maybe LToken)
lexer1_ws
  = (Nothing <$ whitespace)
    <|>
    (Just <$> lexer1)

-- | Lex some whitespace
whitespace :: Lexer ()
whitespace
  = choice [ ignore $ some space
           , block_comment
           , line_comment ]

natural :: Parsec Void Text Nat 
natural = lexeme . try $ do 
  n <-  (some digitChar)
  pure . intToNat . read $ n 


-- | Lex a @{- ... -}@ comment (perhaps nested); consumes no input
-- if the target doesn't start with @{-@.
block_comment :: Lexer ()
block_comment = do
  try $ string_ "{-"
  comment_body

-- | Lex a block comment, without the opening "{-"
comment_body :: Lexer ()
comment_body
  = choice [ block_comment *> comment_body
           , try $ string_ "-}"
           , printChar *> comment_body ]

-- | Lex a line comment
line_comment :: Lexer ()
line_comment = do
  try $ string_ "--"
  ignore $ manyTill printChar (eof <|> ignore newline)

-- | Lex one token
lexer1 :: Lexer LToken
lexer1 = do
  pos <- getSourcePos
  L pos <$> choice [ symbolic
                   , word_token
                   , Nat <$> natural  ]

-- | Lex one non-alphanumeric token
symbolic :: Lexer Token
symbolic = choice [ LBracket <$ char '[' 
                  , RBracket <$ char ']' 
                  , LCurly   <$ char '{' 
                  , RCurly   <$ char '}'
                  , Pipe     <$ char '|'
                  , Comma    <$ char ','
                  , ConsSym  <$ try (string "::") -- if something breaks it's prolly this 
                  , LParen  <$  char '('
                  , RParen  <$  char ')'
                  , Lambda  <$  char '\\'
                  , Dot     <$  char '.'
                  , WildCard <$ char '_'
                  , DblArrow   <$  try (string "=>") -- char '.'
                  , Arrow   <$  try (string "->")
                  , Colon   <$  char ':'
                  , BinOp <$> op2
                  , Assign  <$  char '='
                  , Semi    <$  char ';' ]

op2 :: Lexer Op2
op2 = choice [  AppendOp    <$ try (string "++")
             , PlusOp   <$ char '+'
             , MinusOp  <$ char '-' 
             , TimesOp  <$ char '*' 
             , DivideOp <$ char '/'
             , ModOp    <$ char '%'
             , MapOp    <$ try (string "<$>")
             , LessEqOp <$ try (string "<=")
             , LessOp   <$ char '<' 
             , GreaterEqOp <$ try (string ">=")
             , GreaterOp   <$ char '<' 
             , EqOp        <$ try (string "==")
             , AndOp       <$ try (string "&&")
             , OrOp        <$ try (string "||") ]

fun1 :: Lexer Fun1 
fun1 = choice [ LengthFun  <$ try (string "length")
              , NullFun    <$ try (string "null")
              , SumFun     <$ try (string "sum")
              , ProductFun <$ try (string "product")
              , AndFun     <$ try (string "and")
              , OrFun      <$ try (string "or")
              , NotFun     <$ try (string "not")
              , FstFun     <$ try (string "fst")
              , SndFun     <$ try (string "snd")]

fun2 :: Lexer Fun2 
fun2 = choice [ FilterFun <$ try (string "filter")
              , AllFun    <$ try (string "all")
              , AnyFun    <$ try (string "any")
              , ElemFun   <$ try (string "elem")
              , ReplicateFun <$ try (string "replicate")
              , ForFun       <$ try (string "for")]
{--
-- | Lex one arithmetic operator
arith_op :: Lexer UArithOp
arith_op = choice [ UArithOp Plus     <$ char '+'
                  , UArithOp Minus    <$ char '-'
                  , UArithOp Times    <$ char '*'
                  , UArithOp Divide   <$ char '/'
                  , UArithOp Mod      <$ char '%'
                  , UArithOp LessE    <$ try (string "<=")
                  , UArithOp Less     <$ char '<'
                  , UArithOp GreaterE <$ try (string ">=")
                  , UArithOp Greater  <$ char '>'
                  , UArithOp Equals   <$ try (string "==")]
--}
-- | Lex one alphanumeric token
word_token :: Lexer Token
word_token = to_token <$> word
  where
    to_token :: Text -> Token 
    to_token "true"  = Bool True
    to_token "false" = Bool False
    to_token "if"    = If
    to_token "then"  = Then
    to_token "else"  = Else
    to_token "case"  = Case 
    to_token "of"    = Of 
  --- new stuff here 
    to_token "length" = Fun1T LengthFun
    to_token "null"   = Fun1T NullFun 
    to_token "sum"    = Fun1T SumFun 
    to_token "product" = Fun1T ProductFun 
    to_token "and"     = Fun1T AndFun 
    to_token "or"      = Fun1T OrFun 
    to_token "not"     = Fun1T NotFun 
    to_token "filter"  = Fun2T FilterFun 
    to_token "all"     = Fun2T AllFun 
    to_token "any"     = Fun2T AnyFun 
    to_token "elem"    = Fun2T ElemFun 
    to_token "replicate" = Fun2T ReplicateFun 
    to_token "for"       = Fun2T ForFun 
    to_token "type"      = TypeT 
    to_token "L"         = LTok 
    to_token "R"         = RTok 
    to_token "dec"       = DecT 
  --  to_token "fix"   = FixT
    to_token other   = case unpack other of 
      (x:xs) ->  case fromString (unpack other) of 
        Just lbl -> if isUpper x then Constructor lbl else Name lbl
        Nothing  -> error $ "Unable to parse " 
                        <>  (unpack other)
                        <> "as a label. Labels may only include uppercase and lowercase "
                        <> "letter characters "
      _ -> error  "No input!"

-- | Lex one word
word :: Lexer Text
word = pack <$> ((:) <$> (letterChar <|> char '_') <*>
                 many (alphaNumChar <|> char '_'))
