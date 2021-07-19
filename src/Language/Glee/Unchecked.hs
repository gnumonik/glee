{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds,
             GADTs, RankNTypes, FlexibleInstances, OverloadedStrings, TemplateHaskell #-}
             

module Language.Glee.Unchecked ( UExp(..) ) where

import Language.Glee.Pretty
import Language.Glee.Type
import Language.Glee.Token
import Language.Glee.Util
import Language.Glee.Nat 
import Data.Singletons 
import qualified Data.List as List

import Text.PrettyPrint.ANSI.Leijen
import Data.Text
import Language.Glee.Ascii (Label, toString)
import Language.Glee.Pat 
-- | Unchecked expression
data UExp
  = UVar Int   -- ^ de Bruijn index for a variable

  | UGlobal Label

  | UDataCon Label UExp

  | ULam Ty UExp

  | UApp UExp UExp

  | UCons UExp UExp 

  | UNil (Maybe Ty)

  | UBinOp UExp Op2 UExp 

  | UCond UExp UExp UExp

  | UCase UExp [(Pat,UExp)]

  | URec [(UExp,UExp)]

  | UProject UExp UExp 
  
  | UNatE Nat
  
  | UBoolE Bool deriving (Show)


instance Pretty UExp where
  pretty = defaultPretty
instance PrettyExp UExp where
  prettyExp = prettyExpr

prettyExpr :: Coloring -> Prec -> UExp -> Doc
prettyExpr c _    (UVar n)                     = prettyVar c n
prettyExpr _ _    (UGlobal n)                  = text $ toString n
prettyExpr c prec (UCons e1 e2)                = text "[" <> go e2
  where 
    go x = case x of 
      UCons x1 x2 -> prettyExpr c prec x1 <+> go x2 
      UNil  ty      -> text "]:" <> pretty ty
      _             -> error "Malformed list expression"  

prettyExpr c prec (UNil t) = "[]:" <+> pretty t
prettyExpr c prec (ULam ty body)               = prettyLam c prec (Just ty) body
prettyExpr c prec (UApp e1 e2)                 = prettyApp c prec e1 e2

prettyExpr c prec (UDataCon l e1)              = case e1 of 
  URec [] -> text (toString l)
  _       -> text (toString l) <+> prettyExpr c prec e1              

prettyExpr c prec (UCase e1 ms)              =  text "case" 
                                               <+> prettyExpr c prec e1
                                               <+> "of"
                                               <$$> indent 2 (vcat $ go ms)
  where 
    go :: [(Pat,UExp)] -> [Doc] 
    go [] = []
    go ((p,u):rest) = (prettyPat p <+> text "=>" <+> prettyExpr c prec u) : go rest 

    prettyPat :: Pat -> Doc 
    prettyPat p = case p of 
      VarP l -> text (toString l)
      ConP l p' -> text (toString l) <+> prettyPat p' 
      RecP fps  -> char '{' <+> prettyFieldPats fps <+> char '}' 
      NatP n    -> int (natToInt n)
      BoolP b   -> pretty (UBoolE b)
      WildP     -> char '_' 

    prettyFieldPats :: [(Label,Pat)] -> Doc 
    prettyFieldPats [] = text ""
    prettyFieldPats (f:fs) = case f of 
      (l, pat) -> text (toString l) 
                    <> char ':' 
                    <+> prettyPat pat 
                    <> case fs of 
                          [] -> text ""
                          _  -> char ',' <+> prettyFieldPats fs   

prettyExpr c prec (UCond e1 e2 e3)             = prettyIf c prec e1 e2 e3

prettyExpr c prec (UBinOp e1 op e2)            = prettyExpr c prec e1 
                                               <+> pretty op 
                                               <+> prettyExpr c prec e2 

prettyExpr c prec (UProject e1 e2)             = prettyExpr c prec e1 
                                               <> char '.'
                                               <> prettyExpr c prec e2
prettyExpr _ _    (UNatE n)                    = int $ natToInt n
prettyExpr _ _    (UBoolE True)                = text "true"
prettyExpr _ _    (UBoolE False)               = text "false"

prettyExpr c prec (URec fs)                    = char '{' 
                                               <> hcat (List.intersperse (char ',') $ Prelude.map go fs) 
                                               <> char '}'
  where 
    go (e1,e2) = prettyExpr c prec e1 <> char ':' <> prettyExpr c prec e2  

