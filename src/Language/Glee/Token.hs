{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections, GADTs, StandaloneDeriving, DataKinds, RankNTypes #-}


module Language.Glee.Token  {-- (

  -- * Arithmetic operators
  ArithOp(..), UArithOp(..), eqArithOp,

  -- ** Unchecked synonyms for arithmetic operators
  uPlus, uMinus, uTimes, uDivide, uMod, uLess, uLessE,
  uGreater, uGreaterE, uEquals,

  -- * Tokens
  Token(..), LToken(..), unLoc, unArithOp, unNat, unBool, unName
  ) --}where

import Language.Glee.Type
import Language.Glee.Util
import Language.Glee.Nat 
import Text.PrettyPrint.ANSI.Leijen  as Pretty
import Text.Megaparsec.Pos ( SourcePos )
import Data.Singletons 

import Data.List                      as List
import Data.Text (unpack, pack, Text)
import Language.Glee.Ascii 


data UOp2 where 
  UOp2 :: Op2 -> UOp2 

instance Eq UOp2 where 
  (UOp2 x) == (UOp2 y) =  x == y

data UFun1 where 
  UFun1 :: Fun1 -> UFun1 

instance Eq UFun1 where 
  (UFun1 x) == (UFun1 y) = x == y  

data UFun2 where 
  UFun2 :: Fun2 -> UFun2 

instance Eq UFun2 where 
  (UFun2 x) == (UFun2 y) = x == y 




-- these might need an ITy constraint for the type vars 
data Op2 =
    PlusOp
  | MinusOp
  | TimesOp
  | DivideOp
  | ModOp 
  | LessOp
  | LessEqOp
  | GreaterOp
  | GreaterEqOp 
  | AndOp 
  | OrOp                               
 -- ConsOp                              
  | AppendOp                                  
  | MapOp                                    
  | EqOp deriving (Show, Ord)                                     

instance Eq Op2  where 
   PlusOp == PlusOp           = True 
   MinusOp == MinusOp         = True
   TimesOp == TimesOp         = True 
   DivideOp == DivideOp       = True  
   ModOp == ModOp             = True 
   LessOp == LessOp           = True 
   LessEqOp == LessEqOp       = True 
   GreaterOp == GreaterOp     = True 
   GreaterEqOp == GreaterEqOp = True 
   AndOp == AndOp             = True 
   OrOp == OrOp               = True 
   AppendOp == AppendOp       = True 
   MapOp == MapOp             = True 
   EqOp == EqOp               = True 
   _ == _                     = False 

data Fun1 = 
    LengthFun  -- :: Fun1 -- (List ty) Nat
  | NullFun    -- :: Fun1 -- (List ty) Bool 
  | SumFun     -- :: Fun1 -- (List Nat) Nat 
  | ProductFun -- :: Fun1 -- (List Nat) Nat 
  | AndFun     -- :: Fun1 -- (List Bool) Bool 
  | OrFun      -- :: Fun1 -- (List Bool) Bool 
  | NotFun     -- :: Fun1 -- Bool Bool 
  | FstFun
  | SndFun
    deriving (Eq, Ord)

data Fun2 = 
    FilterFun
  | AllFun
  | AnyFun -- :: Fun2 (ty -> Bool) (List ty) Bool 
  | ElemFun      -- :: Fun2 ty (List ty) Bool 
  | ReplicateFun -- :: Fun2 Nat ty (List ty)
  | ForFun       -- :: Fun2 (ty1 -> ty2) (List ty1) (List ty2)
    deriving (Eq, Ord) 

-- | A lexed token
data Token
  = LBracket 
  | RBracket
  | Pipe 
  | LCurly 
  | RCurly 
  | ConsSym 
  | Comma 
  | LParen
  | RParen
  | Lambda
  | Dot
  | Arrow
  | DblArrow 
  | Colon
  | WildCard 
  | DecT 
  | BinOp Op2
  | Fun1T Fun1 
  | Fun2T Fun2
  | Nat Nat
  | Bool Bool
  | If
  | Then
  | Else
  | Let 
  | In
  | TypeT
 --  | FixT
  | Assign
  | Semi
  | Constructor Label 
  | Name Label
  | Case 
  | Of 
  | LTok 
  | RTok
    deriving (Eq, Ord)
    
-- | Perhaps extract an 'Int'
unNat :: Token -> Maybe Nat
unNat (Nat x) = Just x
unNat _       = Nothing

-- | Perhaps extract an 'Bool'
unBool :: Token -> Maybe Bool
unBool (Bool x) = Just x
unBool _        = Nothing

-- | Perhaps extract a 'Text'
unName :: Token -> Maybe Label
unName (Name x) = Just x
unName _        = Nothing

-- | Perhaps extract a Constructor Label 
unConstr :: Token -> Maybe Label 
unConstr (Constructor l) = Just l 
unConstr _               = Nothing 

-- | A lexed token with location information attached
data LToken = L SourcePos Token deriving Eq

instance Ord LToken where 
  (L s t) <= (L s' t') = s <= s' 

-- | Remove location information from an 'LToken'
unLoc :: LToken -> Token
unLoc (L _ t) = t


instance Pretty Op2 where
  pretty PlusOp      = char '+'
  pretty MinusOp     = char '-'
  pretty TimesOp     = char '*'
  pretty DivideOp    = char '/'
  pretty ModOp       = char '%'
  pretty LessOp      = char '<'
  pretty LessEqOp    = text "<="
  pretty GreaterOp   = char '>'
  pretty GreaterEqOp = text ">="
  pretty EqOp        = text "=="
  pretty AndOp       = text "&&"
  pretty OrOp        = text "||"
  pretty AppendOp    = text "++"
  pretty MapOp       = text "<$>"

instance Pretty Fun1 where 
  pretty LengthFun  = text "length"
  pretty NullFun    = text "null"
  pretty SumFun     = text "sum"
  pretty ProductFun = text "product"
  pretty AndFun     = text "and"
  pretty OrFun      = text "or"
  pretty NotFun     = text "not"
  pretty FstFun     = text "fst"
  pretty SndFun     = text "snd"
  
instance Pretty Fun2 where 
  pretty FilterFun    = text "filter"
  pretty AllFun       = text "all"
  pretty AnyFun       = text "any"
  pretty ElemFun      = text "elem"
  pretty ReplicateFun = text "replicate"
  pretty ForFun       = text "for"

instance Pretty Token where
  pretty     = getDoc . printingInfo
  prettyList = printTogether . List.map printingInfo

instance Show Token where
  show = render . pretty

instance Pretty LToken where
  pretty     = pretty . unLoc
  prettyList = prettyList . List.map unLoc

instance Show LToken where
  show = render . pretty

type PrintingInfo = (Doc, Bool, Bool)
   -- the bools say whether or not to include a space before or a space after

alone :: Doc -> PrintingInfo
alone = (, True, True)

getDoc :: PrintingInfo -> Doc
getDoc (doc, _, _) = doc

printingInfo :: Token -> PrintingInfo
printingInfo LBracket     = (char '[', True,False)
printingInfo RBracket     = (char ']', False, True)
printingInfo LCurly       = (char '{', True,False)
printingInfo RCurly       = (char '}', False,True)
printingInfo Pipe         = (char '|', True,True)
printingInfo Comma        = alone $ text "\',\'"
printingInfo ConsSym      = alone $ text "::"
printingInfo LParen       = (char '(', True, False)
printingInfo RParen       = (char ')', False, True)
printingInfo Lambda       = (char '\\', True, False)
printingInfo DblArrow     = alone $ text "=>"
printingInfo Dot          = (char '.', False, True)
printingInfo Arrow        = alone $ text "->"
printingInfo Colon        = (char ':', False, False)
printingInfo WildCard     = (char '_',True,True)
--printingInfo (ArithOp a)  = alone $ pretty a
printingInfo (Nat i)      = alone $ int (natToInt i)
printingInfo (Bool True)  = alone $ text "true"
printingInfo (Bool False) = alone $ text "false"
printingInfo If           = alone $ text "if"
printingInfo Then         = alone $ text "then"
printingInfo Else         = alone $ text "else"
printingInfo Case         = alone $ text "case"
printingInfo Of           = alone $ text "of"
printingInfo LTok         = (char 'L', False,True)
printingInfo RTok         = (char 'R', False,True)
-- printingInfo FixT         = alone $ text "fix"
printingInfo Assign       = alone $ text "="
printingInfo Semi         = (char ';', False, True)
printingInfo (Fun1T f1)    = alone $ pretty f1
printingInfo (Fun2T f2)    = alone $ pretty f2 
printingInfo (BinOp o)     = alone $ pretty o 
printingInfo (Name t)     = alone $ text (toString t)
printingInfo (Constructor t)     = alone $ text (toString t)
printingInfo TypeT         = alone $ text "type"
printingInfo DecT          = alone $ text "dec"
printingInfo Let           = alone $ text "let"
printingInfo In            = alone $ text "in"

printTogether :: [PrintingInfo] -> Doc
printTogether []  = Pretty.empty
printTogether pis = getDoc $ List.foldl1 combine pis
  where
    combine (doc1, before_space, inner_space1) (doc2, inner_space2, after_space)
      | inner_space1 && inner_space2
      = (doc1 <+> doc2, before_space, after_space)

      | otherwise
      = (doc1 <> doc2, before_space, after_space)
