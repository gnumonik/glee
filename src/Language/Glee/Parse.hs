{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell #-}

module Language.Glee.Parse (
  parseStmtsG,
   parseStmts,
  parseStmtG, parseExpG,
  parseStmt, parseExp --, parse
  ) where

import Language.Glee.Unchecked
import Language.Glee.Statement
import Language.Glee.Token
import Language.Glee.Type
import Language.Glee.Monad
import Language.Glee.Lex (lexG)
import Language.Glee.Util
import Language.Glee.Globals 
import qualified Text.Megaparsec as Parsec hiding ( parse )
import Text.Megaparsec.Pos
import Text.Megaparsec
    ( (<|>),
      runParserT,
      between,
      choice,
      option,
      sepBy,
      sepEndBy,
      some,
      MonadParsec(try, eof, token, label),
      ErrorFancy(..),
      ErrorItem(..),
      ParseError(..),
      ParseErrorBundle(bundlePosState, bundleErrors),
      ShowErrorComponent(showErrorComponent),
      ParsecT,
      PosState(pstateInput) )

import Text.PrettyPrint.ANSI.Leijen hiding ( (<$>) )
import Data.Set as Set  
import Data.List as List
import Control.Lens.TH 
import Data.List.NonEmpty as DL
import qualified Data.Map as M 
import Control.Lens hiding (Context)
import Control.Arrow as Arrow ( left )
import Control.Monad.Reader
import Data.Text (unpack, pack, Text)
import Data.Void
import Control.Applicative (Alternative)
import Control.Monad.Combinators.Expr
    ( makeExprParser,
      Operator(Postfix, InfixN, InfixL, InfixR, Prefix) )
import Control.Monad.Combinators 
import Language.Glee.Ascii
import Data.Map
import Data.Singletons
import Data.Singletons.TypeLits
import Language.Glee.Hasochism
import Data.Singletons.Prelude.List
import Language.Glee.Pat 
import Text.Megaparsec.Debug



testSym = $(mkSomeSymbol "Hello")

table :: [[Operator Parser UExp]]
table = [ [project]
        ,  [binary ConsSym UCons]
        , [arOp]
        ]

project :: Operator Parser UExp  
project = InfixN . tok' $ \case 
  Dot -> Just $ \record lbl -> UProject record lbl 
  _   -> Nothing 

opParser :: Parser UExp 
opParser = label "A binary operator" $ makeExprParser term  table 

arOp :: Operator Parser UExp
arOp = InfixL $ (tok' (\case {BinOp x -> Just $ \e1 e2 -> UBinOp e1 x e2 ; _ -> Nothing}))

binary :: Token -> (a -> a -> a) -> Operator Parser a
binary t f = InfixR $ tok t >> pure f 

prefix :: Token -> (a -> a) -> Operator Parser a
prefix t f = Prefix $ tok t >> pure f 

postfix :: Token -> Parser (a -> a) -> Operator Parser a
postfix t f = Postfix $  tok t >> f 

---- write a real expr parser at some point but for now:

chainl1 :: (Alternative m, Monad m) => m t -> m (t -> t -> t) -> m t
chainl1 p op        = do{ x <- p; rest x }
                    where
                      rest x    = do{ f <- op
                                    ; y <- p
                                    ; rest (f x y)
                                    }
                                <|> return x
{-# INLINE chainl1 #-}

chainr1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainr1 p op = scan where
  scan = flip id <$> p <*> rst
  rst  = (flip <$> op <*> scan) <|> pure id
{-# INLINE chainr1 #-}

-- | Parse a sequence of semicolon-separated statements, aborting with
-- an error upon failure
parseStmtsG :: [LToken] -> GlamE [Statement]
parseStmtsG ts = ask >>= \e -> 
  eitherToGlamE (parseWithContext (e ^. globalContext) stmts ts)

-- | Parse a sequence of semicolon-separated statements
parseStmts :: Context -> [LToken] -> Either Doc [Statement]
parseStmts ctx ts = parseWithContext ctx stmts ts 

-- | Parse a 'Statement', aborting with an error upon failure
parseStmtG :: [LToken] -> GlamE Statement
parseStmtG ts = asks (view globalContext) >>= \ctx -> 
  eitherToGlamE . parseStmt ctx $ ts 

-- | Parse a 'Statement'
parseStmt :: Context -> [LToken] -> Either Doc Statement
parseStmt ctx = parseWithContext ctx  stmt

-- | Parse a 'UExp', aborting with an error upon failure
parseExpG :: [LToken] -> GlamE UExp
parseExpG ts = ask >>= \e -> eitherToGlamE (parseWithContext (e ^. globalContext) expr ts)

-- | Parse a 'UExp'
parseExp :: Context -> [LToken] -> Either Doc UExp
parseExp ctx ts = parseWithContext ctx expr ts 

parseWithContext :: Context -> Parser a -> [LToken] -> Either Doc a 
parseWithContext cxt p tokens = Arrow.left ( prettyBundle) $
                 runReader (runParserT (p <* eof) "" tokens) cxt


--parse :: Parser a -> [LToken] -> Either Doc  a
--parse p tokens = parseWithContext initContext p tokens 


prettyBundle :: ParseErrorBundle [LToken] Void -> Doc 
prettyBundle bundle =  text "Error:" <+> highlightErr 
                   <$$> goErrs 
  where 
    pState = bundlePosState bundle

    pStream = pstateInput pState 

    highlightErr :: Doc 
    highlightErr = list . List.reverse $ List.foldl' (\acc (i,x) -> 
                            if i == errPos 
                            then (red . text $ show x) : acc 
                            else text (show x) : acc) [] (List.zip [0..] pStream) 
    prettyList :: [Doc] -> Doc  
    prettyList [] = red $ text "<NO INPUT>"
    prettyList xs = List.foldl' (\acc (x :: Doc) ->  acc <+> x <+> char ',') (text "") xs 



    bErrs = bundleErrors bundle 

    errPos  = case DL.head bErrs of 
        TrivialError n _ _ -> n 
        FancyError n _     -> n 
    goErrs =  vcat $ List.map (text . showErrorComponent) . DL.toList $ bErrs 



instance Ord (ParseError [LToken] Void) where 
  errA <= errB =
    let xA = case errA of 
                TrivialError n _ _ -> n 
                FancyError n _     -> n 
        xB = case errB of 
                TrivialError n _ _ -> n 
                FancyError n _     -> n 
    in xA <= xB 

instance ShowErrorComponent (ParseError [LToken] Void) where
  showErrorComponent x = case x of 
    TrivialError offset unexp expec -> 
      "Error at token #" 
      <> show offset
      <> "\n" 
      <> ("Unexpected: " <> maybe "" prettyErrItem unexp)
      <> "\n"
      <> ("Expecting: " <> prettyErrSet expec) 
      <> "\n"

    FancyError offset fancy -> 
         "Error at token #" 
      <> show offset
      <> "\n"
      <> "Error Info: "
      <> (List.concatMap prettyFancy $ Set.toList fancy)
   where 
     prettyFancy :: ErrorFancy Void -> String  
     prettyFancy = \case 
      ErrorFail str -> str 
      ErrorIndentation {} -> "Incorrect indentation!"
      ErrorCustom v -> show v 

prettyErrItem :: ErrorItem (Parsec.Token [LToken]) -> String 
prettyErrItem x = case x of 
  Tokens t -> show . DL.head $ t 
  EndOfInput -> "End of Input" 

  Label cs -> show . DL.toList $ cs 

prettyErrSet :: Set (ErrorItem (Parsec.Token [LToken])) -> String 
prettyErrSet s = 
  let l = Set.toList s 
      x = List.map prettyErrItem l 
      r = concat $ List.intersperse ", " x 
  in r 
----------------------


-- Plumbing

-- the "state" is a list of bound names. searching a bound name in the list
-- gives you the correct deBruijn index
type Parser = ParsecT Void [LToken] (Reader Context)

-- | Bind a name over an expression
bind :: Label -> Parser a -> Parser a
bind bound_var  = local (over boundNames (bound_var :)) 

-- | Parse the given nullary token
tok :: Token -> Parser ()
tok t = void $ token  myToken expected 
  where 
    myToken x = if unLoc x == t then Just x else Nothing 

    expected = Set.empty -- fix later 

-- | Parse the given unary token
tok' :: (Token -> Maybe thing) -> Parser thing
tok' matcher = token (matcher . unLoc) expected 
  where 
    expected = Set.empty -- fix later 

{--
-- | Parse one of a set of 'ArithOp's
arith_op :: [UArithOp] -> Parser UArithOp
arith_op ops = token myToken (Set.empty)
  where 
    myToken = \case L _ (ArithOp op) | op `elem` ops -> Just op
                    _                                -> Nothing
bop :: Functor f =>  a -> f b -> f a
bop = (<$)

--}

next_pos :: SourcePos  -- ^ position of the current token
         -> LToken     -- ^ current token
         -> [LToken]   -- ^ remaining tokens
         -> SourcePos  -- ^ location of the next token
next_pos pos _ []            = pos
next_pos _   _ (L pos _ : _) = pos

--------------
-- Real work

stmts :: Parser [Statement]
stmts = stmt `sepEndBy` tok Semi

stmt :: Parser Statement
stmt = choice [ try tyDec 
              , try funDecSugar -- try $ NewGlobal <$> tok' unName <* tok Assign <*> expr
              , BareExp <$> expr ]



funDecSugar :: Parser Statement 
funDecSugar = do 
 -- tok DecT 
  l <- tok' unName 
  ps <- many typedArg 
  tok Assign 
  NewGlobal l <$> go ps  
 where 
   typedArg :: Parser (Label,Ty)
   typedArg = (,) <$> tok' unName <* tok Colon <*> ty 

   go :: [(Label,Ty)] -> Parser UExp 
   go [] = expr 
   go ((v,t):xs) = local (over boundNames (v:)) $ ULam t <$> go xs 

expr :: Parser UExp
expr = label "An Expression" $ choice [ 
                dataCon 
              , lam
              , cond
              , caseE
              , opParser

              --, int_exp `chainl1` bool_op 
              --, listSugar
              ]

--int_exp :: Parser UExp
--int_exp = term `chainl1` add_op

term :: Parser UExp
term = apps  --`chainl1` mul_op

apps :: Parser UExp
apps = -- choice [ --UFix <$ tok FixT <*> expr ,
               List.foldl1 UApp <$> some factor -- ]

factor :: Parser UExp
factor = choice [ try dataCon 
                , between (tok LParen) (tok RParen) expr
                , label "A Nat Literal" $ UNatE <$> tok' unNat
                , label "A Bool Literal" $ UBoolE <$> tok' unBool
                , var
                , listSugar 
                , record ]

lam :: Parser UExp
lam = label "A Lambda Expression" $ do
  tok Lambda
  bound_var <- tok' unName
  tok Colon
  typ <- arg_ty
  tok Arrow
  e <- bind bound_var expr
  return (ULam typ e)


record :: Parser UExp 
record = label "A record" 
       $ between (tok LCurly) (tok RCurly) 
       $ URec <$> (recField `sepBy` (tok Comma)) 
  where 
    recField :: Parser (UExp,UExp)
    recField = do 
      e1 <- expr 
      tok Colon 
      e2 <- expr 
      pure $ (e1,e2)


dataCon :: Parser UExp 
dataCon = label "A data constructor" $ do 
  l <- tok' unConstr 
  SomeSing l' <- pure $ toSing l 
  readDataCon l' >>= \case 
    -- for enums w/ no argument. RecTy [] = Unit, RZ = unit  
    Just (MkConstructor sl (SRecTy SNil) _ ) -> pure $ UDataCon l (URec []) 
    Just _          -> do 
      e1 <- expr 
      pure $ UDataCon l e1 
    Nothing -> do 
      let lStr = toString l 
      fail $ "Error: " <> lStr <> " is not a known data constructor of a variant."
--- problem is that datacons arent being generated for sum type decls 
readDataCon :: MonadReader Context m => Sing (l :: Label) -> m (Maybe (ConstructorInfo l))
readDataCon l = asks (view dataCons) >>= \case  
  Some hlist -> pure $ hLookup l hlist 

cond :: Parser UExp
cond = label "A Conditional Expression" 
     $ UCond <$ tok If <*> expr <* tok Then <*> expr <* tok Else <*> expr

caseE :: Parser UExp 
caseE = label  "A case expression" $ do 
  tok Case 
  arg <- expr 
  tok Of 
  matches <- match `sepBy1` tok Pipe 
  pure $ UCase arg matches    

pat :: Parser Pat 
pat = label "A pattern" $ choice [conP
             , varP 
             ,recP 
             ,natP 
             ,boolP 
             ,wildP]
  where 
    varP :: Parser Pat 
    varP =  label "A variable pattern" $ VarP <$> tok' unName 

    conP :: Parser Pat 
    conP = label "A Constructor pattern" $ do 
      l <- tok' unConstr
      SomeSing l' <- pure $ toSing l 
      readDataCon l' >>= \case 
        Just (MkConstructor _ (SRecTy SNil) _ ) -> pure $ ConP l (RecP [])
        Just _ -> try $ do 
          p <- pat 
          pure $ ConP l p 
        Nothing -> fail $  "Error: " <> toString l <> " is not a known data constructor of a variant."

    recP :: Parser Pat 
    recP = label "A Record Pattern" $ between (tok LCurly) (tok RCurly) $ RecP <$> (fieldP `sepBy` tok Comma)

    fieldP :: Parser (Label,Pat)
    fieldP = label "A Field Pattern" $ (,) <$> (tok' unName) <* tok Colon <*> pat 

    natP :: Parser Pat 
    natP = label "A Nat Literal Pattern" $ NatP <$> tok' unNat 

    boolP :: Parser Pat 
    boolP = label "A Bool Literal Pattern" $ BoolP <$> tok' unBool 

    wildP :: Parser Pat 
    wildP = label "A WildCard Pattern" $ WildP <$ tok WildCard 

match :: Parser (Pat,UExp)
match = label "A Match Expression" $ do 
  p <- pat
  tok Arrow 
  bindPatVars p expr
 where 
  bindPatVars :: Pat -> Parser a -> Parser (Pat,a) 
  bindPatVars pat prsr = do 
     let ls = getVars pat 
     (pat,) <$> local (over boundNames (ls <>)) prsr 

  getVars :: Pat -> [Label]
  getVars p = case p of 
    VarP l -> [l]
    WildP  -> [] -- might be wrong?
    ConP l p -> getVars p 
    RecP fps -> getFieldVars fps 
    _ -> []

  getFieldVars :: [(Label,Pat)] -> [Label]
  getFieldVars fs = List.foldl' (\acc (_, p) -> acc <> getVars p) [] fs 

var :: Parser UExp
var = label "A variable name" $ do
  n <- tok' unName
  m_index <- asks (elemIndex n . view boundNames)
  case m_index of
    Nothing -> return (UGlobal n)
    Just i  -> return (UVar i)

ty :: Parser Ty
ty = label "A Type" $ chainr1 arg_ty ((:->) <$ tok Arrow)

tyDec :: Parser Statement 
tyDec = do 
  tok TypeT 
  l <- tok' unConstr 
  tok Assign 
  t <- sumDecl <|> ty --(between (tok LParen) (tok RParen) sumDecl) <|> ty 
  pure $ TyDec l t 

sumDecl :: Parser Ty 
sumDecl = VariantTy <$> (go `sepBy1` tok Pipe) 
  where 
    go :: Parser (Label,Ty)
    go = do 
      l <- tok' unConstr
      t <- option (RecTy []) ty 
      pure (l,t)


arg_ty :: Parser Ty
arg_ty = choice [ try recTy 
                , try tycon 
                , between (tok LParen) (tok RParen) ty]

tycon :: Parser Ty
tycon = do
  n <-  tok' unConstr
  case toString n of 
    "List" -> do 
       listOf <- ty 
       pure $ ListTy listOf 
    _ -> readTyCon' n >>= \case 
      Nothing -> fail $ render $ -- fix 
                text "Type Constructor not in scope:" <+> squotes (text . toString $ n)
      Just ty -> return ty



readTyCon' :: MonadReader Context m => Label -> m (Maybe Ty)
readTyCon' l = asks (M.lookup l . view types)

recTy :: Parser Ty 
recTy = label "A record type. E.g. {count: Nat, switch: Bool}" 
      $ between (tok LCurly) (tok RCurly) 
      $ RecTy <$> (recField `sepBy` tok Comma)
  where 
    recField :: Parser (Label,Ty)
    recField = do 
      l <- tok' unName 
      tok Colon 
      t <- ty -- if this breaks it's cuz this should be arg_ty 
      pure $ (l,t)

consSugar :: Parser UExp 
consSugar = apps `chainr1` go
  where 
    go = do 
      tok ConsSym 
      pure $ \e1 e2 -> UCons e1 e2 

listSugar :: Parser UExp 
listSugar = label "A List" $ do 
  content <- between (tok LBracket) (tok RBracket) (sepBy  expr (tok Comma))
  case content of 
    [] -> do 
      x <- option Nothing $ Just <$> (try $ tok Colon)
      case x of 
          Nothing -> pure $ UNil Nothing 
          Just _ -> do 
            typ <- ty 
            pure . UNil . Just $ typ 
    xs -> pure $ List.foldr UCons (UNil Nothing) xs 
              

{--
add_op, mul_op, bool_op :: Parser (UExp -> UExp -> UExp)
add_op = mk_op <$> arith_op [uPlus, uMinus]
mul_op = mk_op <$> arith_op [uTimes, uDivide, uMod]
bool_op = mk_op <$> arith_op [uLess, uLessE, uGreater, uGreaterE, uEquals]

mk_op :: UArithOp -> UExp -> UExp -> UExp
mk_op op e1 e2 = UArith e1 op e2
--}