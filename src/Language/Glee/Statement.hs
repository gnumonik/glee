

module Language.Glee.Statement ( Statement(..) ) where

import Language.Glee.Unchecked

import Text.PrettyPrint.ANSI.Leijen
import Data.Text
import Language.Glee.Ascii
import Language.Glee.Type 

-- | A statement can either be a bare expression, which will be evaluated,
-- or an assignment to a global variable.
data Statement = BareExp UExp
               | NewGlobal Label UExp
               | TyDec Label Ty 

instance Pretty Statement where
  pretty (BareExp exp)     = pretty exp
  pretty (NewGlobal v exp) = text (toString v) <+> char '=' <+> pretty exp
  pretty (TyDec l t)       =  text "type" 
                          <+> text (toString l)
                          <+> pretty t