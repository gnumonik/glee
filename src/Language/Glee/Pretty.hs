{-# LANGUAGE ViewPatterns, GADTs, FlexibleInstances, UndecidableInstances,
             CPP #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
{-# OPTIONS_GHC -fno-warn-unrecognised-pragmas #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}



-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Glee.Pretty
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- Pretty-printing expressions. This allows reduction of code duplication
-- between unchecked and checked expressions.
--
----------------------------------------------------------------------------

module Language.Glee.Pretty (
  PrettyExp(..), defaultPretty,
  Coloring, defaultColoring,
  prettyVar, prettyLam, prettyApp, prettyIf, prettyFix, prettyBinOp
  ) where

import Language.Glee.Token
import Language.Glee.Type
import Language.Glee.Util

import Text.PrettyPrint.ANSI.Leijen

lamPrec, appPrec, appLeftPrec, appRightPrec, ifPrec :: Prec
lamPrec = 1
appPrec = 9
appLeftPrec = 8.9
appRightPrec = 9
ifPrec = 1

-- | A function that changes a 'Doc's color
type ApplyColor = Doc -> Doc

-- | Information about coloring in de Bruijn indexes and binders
data Coloring = Coloring [ApplyColor]
                         [ApplyColor]  -- ^ a stream of remaining colors to use,
                                       -- and the colors used for bound variables

-- | A 'Coloring' for an empty context
defaultColoring :: Coloring
defaultColoring = Coloring all_colors []
  where
    all_colors = red : green : yellow : blue :
                 magenta : cyan : all_colors

-- | A class for expressions that can be pretty-printed
class Pretty exp => PrettyExp exp where
  prettyExp :: Coloring -> Prec -> exp -> Doc

-- | Convenient implementation of 'pretty'
defaultPretty :: PrettyExp exp => exp -> Doc
defaultPretty = nest 2 . prettyExp defaultColoring topPrec

-- | Print a variable
prettyVar :: Coloring -> Int -> Doc
prettyVar (Coloring _ bound) n = nthDefault id n bound (char '#' <> int n)

-- | Print a lambda expression
prettyLam :: PrettyExp exp => Coloring -> Prec -> Maybe Ty -> exp -> Doc
prettyLam (Coloring (next : supply) existing) prec m_ty body
  = maybeParens (prec >= lamPrec) $
    fillSep [ char 'λ' <> next (char '#') <>
              maybe empty (\ty -> text ":" <> pretty ty) m_ty <> text " =>"
            , prettyExp (Coloring supply (next : existing)) topPrec body ]
prettyLam _ _ _ _ = error "Infinite supply of colors ran out"

-- | Print an application
prettyApp :: (PrettyExp exp1, PrettyExp exp2)
          => Coloring -> Prec -> exp1 -> exp2 -> Doc
prettyApp coloring prec e1 e2
  = maybeParens (prec >= appPrec) $
    fillSep [ prettyExp coloring appLeftPrec  e1
            , prettyExp coloring appRightPrec e2 ]

prettyBinOp :: (PrettyExp exp1, PrettyExp exp2)
            => Coloring -> Prec -> exp1 -> Op2 -> exp2 -> Doc 
prettyBinOp coloring prec e1 op e2
  = maybeParens True $
    fillSep [ prettyExp coloring 5 e1 <+> pretty op
            , prettyExp coloring 5 e2 ]

-- | Print a conditional
prettyIf :: (PrettyExp exp1, PrettyExp exp2, PrettyExp exp3)
         => Coloring -> Prec -> exp1 -> exp2 -> exp3 -> Doc
prettyIf coloring prec e1 e2 e3
  = maybeParens (prec >= ifPrec) $
    fillSep [ text "if" <+> prettyExp coloring topPrec e1
            , text "then" <+> prettyExp coloring topPrec e2
            , text "else" <+> prettyExp coloring topPrec e3 ]

{--
prettyCons :: (PrettyExp exp1, PrettyExp exp2)
           => Coloring -> Prec -> exp1 -> exp2 -> Doc 
prettyCons coloring prec e1 e2 
  = maybeParens (prec >= ifPrec) $ 
    fillSep $ [text "["] <> go e2 --}


-- | Print a @fix@
prettyFix :: PrettyExp exp => Coloring -> Prec -> exp -> Doc
prettyFix coloring prec e
  = maybeParens (prec >= appPrec) $
    text "fix" <+> prettyExp coloring topPrec e
