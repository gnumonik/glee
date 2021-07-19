{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeOperators, TypeFamilies,
             ScopedTypeVariables, TypeApplications, TemplateHaskell, EmptyCase, InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Glee.Ascii where

import Data.Singletons.TH

import Language.Haskell.TH
    ( mkName,
      Exp(AppE, ConE, VarE, SigE),
      Q,
      Type(AppT, ConT, LitT),
      TyLit(StrTyLit) ) 
import Data.Constraint ( Dict(..) ) 
import Data.Maybe ( fromJust ) 
import Data.Singletons.Prelude.List ( SList(SCons, SNil) )
import Data.Singletons.Prelude
    (Proxy(..), Symbol, SSemigroup((%<>)), PSemigroup(type (<>)) )
import Data.Singletons.TypeLits ( Symbol )
import Data.Singletons

-- bullshit workaround for the "can't promote strings" thing. mostly codegen'd

$(singletons [d| 
  data DSym = 
      A_ 
    | B_ 
    | C_ 
    | D_ 
    | E_ 
    | F_ 
    | G_ 
    | H_ 
    | I_ 
    | J_ 
    | K_ 
    | L_ 
    | M_ 
    | N_ 
    | O_ 
    | P_ 
    | Q_ 
    | R_ 
    | S_ 
    | T_ 
    | U_ 
    | V_ 
    | W_ 
    | X_ 
    | Y_ 
    | Z_ 
      deriving (Show, Eq, Ord, Enum)
  |])

$(singletons [d| data DCase = Upper | Lower deriving (Show, Eq, Ord, Enum) |])  


$(singletons [d| newtype DChar = DChar {getDChar :: (DCase,DSym)} deriving (Show, Eq, Ord) |])

$(singletons [d| newtype DString = DString [DChar] deriving (Show, Eq, Ord) |]) 


class ValidDataCon (dstr :: DString)

instance ValidDataCon ('DString ('DChar '(Upper,x) ': xs))

isValidDataCon :: Sing (l :: DString) -> Maybe (Dict (ValidDataCon l))
isValidDataCon s = case s of 
  SDString SNil -> Nothing 
  SDString (SCons x xs) -> case x of 
    SDChar (STuple2 SUpper _) -> Just Dict 
    _ -> Nothing 
 
fromString :: String -> Maybe DString 
fromString str = DString <$> mapM fromChar str  
 
toString :: DString -> String 
toString (DString xs) = map toChar xs 

fromChar :: Char -> Maybe DChar 
fromChar x = case x of 
  'a' -> l A_
  'b' -> l B_
  'c' -> l C_
  'd' -> l D_
  'e' -> l E_
  'f' -> l F_
  'g' -> l G_
  'h' -> l H_
  'i' -> l I_
  'j' -> l J_
  'k' -> l K_
  'l' -> l L_
  'm' -> l M_
  'n' -> l N_
  'o' -> l O_
  'p' -> l P_
  'q' -> l Q_
  'r' -> l R_
  's' -> l S_
  't' -> l T_
  'u' -> l U_
  'v' -> l V_
  'w' -> l W_
  'x' -> l X_
  'y' -> l Y_
  'z' -> l Z_
  'A' -> u A_
  'B' -> u B_
  'C' -> u C_
  'D' -> u D_
  'E' -> u E_
  'F' -> u F_
  'G' -> u G_
  'H' -> u H_
  'I' -> u I_
  'J' -> u J_
  'K' -> u K_
  'L' -> u L_
  'M' -> u M_
  'N' -> u N_
  'O' -> u O_
  'P' -> u P_
  'Q' -> u Q_
  'R' -> u R_
  'S' -> u S_
  'T' -> u T_
  'U' -> u U_
  'V' -> u V_
  'W' -> u W_
  'X' -> u X_
  'Y' -> u Y_
  'Z' -> u Z_
  _   -> Nothing 
  where 
    u :: DSym -> Maybe DChar 
    u ds = Just $ DChar (Upper,ds)

    l :: DSym -> Maybe DChar 
    l ds = Just $ DChar (Lower,ds)

toChar :: DChar -> Char 
toChar (DChar c) = case c of 
  (Upper,A_) -> 'A'
  (Lower,A_) -> 'a'
  (Upper,B_) -> 'B'
  (Lower,B_) -> 'b'
  (Upper,C_) -> 'C'
  (Lower,C_) -> 'c'
  (Upper,D_) -> 'D'
  (Lower,D_) -> 'd'
  (Upper,E_) -> 'E'
  (Lower,E_) -> 'e'
  (Upper,F_) -> 'F'
  (Lower,F_) -> 'f'
  (Upper,G_) -> 'G'
  (Lower,G_) -> 'g'
  (Upper,H_) -> 'H'
  (Lower,H_) -> 'h'
  (Upper,I_) -> 'I'
  (Lower,I_) -> 'i'
  (Upper,J_) -> 'J'
  (Lower,J_) -> 'j'
  (Upper,K_) -> 'K'
  (Lower,K_) -> 'k'
  (Upper,L_) -> 'L'
  (Lower,L_) -> 'l'
  (Upper,M_) -> 'M'
  (Lower,M_) -> 'm'
  (Upper,N_) -> 'N'
  (Lower,N_) -> 'n'
  (Upper,O_) -> 'O'
  (Lower,O_) -> 'o'
  (Upper,P_) -> 'P'
  (Lower,P_) -> 'p'
  (Upper,Q_) -> 'Q'
  (Lower,Q_) -> 'q'
  (Upper,R_) -> 'R'
  (Lower,R_) -> 'r'
  (Upper,S_) -> 'S'
  (Lower,S_) -> 's'
  (Upper,T_) -> 'T'
  (Lower,T_) -> 't'
  (Upper,U_) -> 'U'
  (Lower,U_) -> 'u'
  (Upper,V_) -> 'V'
  (Lower,V_) -> 'v'
  (Upper,W_) -> 'W'
  (Lower,W_) -> 'w'
  (Upper,X_) -> 'X'
  (Lower,X_) -> 'x'
  (Upper,Y_) -> 'Y'
  (Lower,Y_) -> 'y'
  (Upper,Z_) -> 'Z'
  (Lower,Z_) -> 'z'

type Label = DString 

mkDString :: String -> Q Exp 
mkDString str = case fromString str of 
  Nothing -> fail $ "Could not render " <> str <> "as a label!\n"
                  <> "A label may only contain upper or lower case alphabetic characters."
  Just l  -> [e| fromJust $ fromString str |]

mkSomeSymbol :: String -> Q Exp 
mkSomeSymbol str = do
  let someSing = ConE . mkName $ "SomeSing"
  let sng      = VarE . mkName $ "sing"
  let sngTyCon = ConT . mkName $ "Sing"
  let sig      = SigE sng (sngTyCon `AppT` (LitT . StrTyLit $ str))
  pure $ AppE someSing (sig)

type CharSym :: DChar -> Symbol 
type family CharSym dChar where 
  CharSym ('DChar '(Upper,A_)) = "A"
  CharSym ('DChar '(Lower,A_)) = "a"
  CharSym ('DChar '(Upper,B_)) = "B"
  CharSym ('DChar '(Lower,B_)) = "b"
  CharSym ('DChar '(Upper,C_)) = "C"
  CharSym ('DChar '(Lower,C_)) = "c"
  CharSym ('DChar '(Upper,D_)) = "D"
  CharSym ('DChar '(Lower,D_)) = "d"
  CharSym ('DChar '(Upper,E_)) = "E"
  CharSym ('DChar '(Lower,E_)) = "e"
  CharSym ('DChar '(Upper,F_)) = "F"
  CharSym ('DChar '(Lower,F_)) = "f"
  CharSym ('DChar '(Upper,G_)) = "G"
  CharSym ('DChar '(Lower,G_)) = "g"
  CharSym ('DChar '(Upper,H_)) = "H"
  CharSym ('DChar '(Lower,H_)) = "h"
  CharSym ('DChar '(Upper,I_)) = "I"
  CharSym ('DChar '(Lower,I_)) = "i"
  CharSym ('DChar '(Upper,J_)) = "J"
  CharSym ('DChar '(Lower,J_)) = "j"
  CharSym ('DChar '(Upper,K_)) = "K"
  CharSym ('DChar '(Lower,K_)) = "k"
  CharSym ('DChar '(Upper,L_)) = "L"
  CharSym ('DChar '(Lower,L_)) = "l"
  CharSym ('DChar '(Upper,M_)) = "M"
  CharSym ('DChar '(Lower,M_)) = "m"
  CharSym ('DChar '(Upper,N_)) = "N"
  CharSym ('DChar '(Lower,N_)) = "n"
  CharSym ('DChar '(Upper,O_)) = "O"
  CharSym ('DChar '(Lower,O_)) = "o"
  CharSym ('DChar '(Upper,P_)) = "P"
  CharSym ('DChar '(Lower,P_)) = "p"
  CharSym ('DChar '(Upper,Q_)) = "Q"
  CharSym ('DChar '(Lower,Q_)) = "q"
  CharSym ('DChar '(Upper,R_)) = "R"
  CharSym ('DChar '(Lower,R_)) = "r"
  CharSym ('DChar '(Upper,S_)) = "S"
  CharSym ('DChar '(Lower,S_)) = "s"
  CharSym ('DChar '(Upper,T_)) = "T"
  CharSym ('DChar '(Lower,T_)) = "t"
  CharSym ('DChar '(Upper,U_)) = "U"
  CharSym ('DChar '(Lower,U_)) = "u"
  CharSym ('DChar '(Upper,V_)) = "V"
  CharSym ('DChar '(Lower,V_)) = "v"
  CharSym ('DChar '(Upper,W_)) = "W"
  CharSym ('DChar '(Lower,W_)) = "w"
  CharSym ('DChar '(Upper,X_)) = "X"
  CharSym ('DChar '(Lower,X_)) = "x"
  CharSym ('DChar '(Upper,Y_)) = "Y"
  CharSym ('DChar '(Lower,Y_)) = "y"
  CharSym ('DChar '(Upper,Z_)) = "Z"
  CharSym ('DChar '(Lower,Z_)) = "z"

sCharSym :: Sing (dChar :: DChar) -> Sing (CharSym dChar)
sCharSym s = case s of 
  SDChar (STuple2 SUpper SA_) -> sing @"A"
  SDChar (STuple2 SLower SA_) -> sing @"a"
  SDChar (STuple2 SUpper SB_) -> sing @"B"
  SDChar (STuple2 SLower SB_) -> sing @"b"
  SDChar (STuple2 SUpper SC_) -> sing @"C"
  SDChar (STuple2 SLower SC_) -> sing @"c"
  SDChar (STuple2 SUpper SD_) -> sing @"D"
  SDChar (STuple2 SLower SD_) -> sing @"d"
  SDChar (STuple2 SUpper SE_) -> sing @"E"
  SDChar (STuple2 SLower SE_) -> sing @"e"
  SDChar (STuple2 SUpper SF_) -> sing @"F"
  SDChar (STuple2 SLower SF_) -> sing @"f"
  SDChar (STuple2 SUpper SG_) -> sing @"G"
  SDChar (STuple2 SLower SG_) -> sing @"g"
  SDChar (STuple2 SUpper SH_) -> sing @"H"
  SDChar (STuple2 SLower SH_) -> sing @"h"
  SDChar (STuple2 SUpper SI_) -> sing @"I"
  SDChar (STuple2 SLower SI_) -> sing @"i"
  SDChar (STuple2 SUpper SJ_) -> sing @"J"
  SDChar (STuple2 SLower SJ_) -> sing @"j"
  SDChar (STuple2 SUpper SK_) -> sing @"K"
  SDChar (STuple2 SLower SK_) -> sing @"k"
  SDChar (STuple2 SUpper SL_) -> sing @"L"
  SDChar (STuple2 SLower SL_) -> sing @"l"
  SDChar (STuple2 SUpper SM_) -> sing @"M"
  SDChar (STuple2 SLower SM_) -> sing @"m"
  SDChar (STuple2 SUpper SN_) -> sing @"N"
  SDChar (STuple2 SLower SN_) -> sing @"n"
  SDChar (STuple2 SUpper SO_) -> sing @"O"
  SDChar (STuple2 SLower SO_) -> sing @"o"
  SDChar (STuple2 SUpper SP_) -> sing @"P"
  SDChar (STuple2 SLower SP_) -> sing @"p"
  SDChar (STuple2 SUpper SQ_) -> sing @"Q"
  SDChar (STuple2 SLower SQ_) -> sing @"q"
  SDChar (STuple2 SUpper SR_) -> sing @"R"
  SDChar (STuple2 SLower SR_) -> sing @"r"
  SDChar (STuple2 SUpper SS_) -> sing @"S"
  SDChar (STuple2 SLower SS_) -> sing @"s"
  SDChar (STuple2 SUpper ST_) -> sing @"T"
  SDChar (STuple2 SLower ST_) -> sing @"t"
  SDChar (STuple2 SUpper SU_) -> sing @"U"
  SDChar (STuple2 SLower SU_) -> sing @"u"
  SDChar (STuple2 SUpper SV_) -> sing @"V"
  SDChar (STuple2 SLower SV_) -> sing @"v"
  SDChar (STuple2 SUpper SW_) -> sing @"W"
  SDChar (STuple2 SLower SW_) -> sing @"w"
  SDChar (STuple2 SUpper SX_) -> sing @"X"
  SDChar (STuple2 SLower SX_) -> sing @"x"
  SDChar (STuple2 SUpper SY_) -> sing @"Y"
  SDChar (STuple2 SLower SY_) -> sing @"y"
  SDChar (STuple2 SUpper SZ_) -> sing @"Z"
  SDChar (STuple2 SLower SZ_) -> sing @"z"
 
type LabelSym :: Label -> Symbol 
type family LabelSym l where 
  LabelSym ('DString '[]) = ""
  LabelSym ('DString (x ': xs)) = CharSym x <> (LabelSym ('DString xs))


class SymLabel (s :: Symbol) (l :: Label) | l -> s  

instance LabelSym l ~ s => SymLabel s l 

sLabelSym :: Sing (l :: Label) -> Sing (LabelSym l)
sLabelSym l = case l of 
  SDString SNil -> sing @""
  SDString (SCons x xs) -> sCharSym x %<> sLabelSym (SDString xs)


liftLabel :: Label -> SomeSing Symbol 
liftLabel l = case toSing l of 
  SomeSing l' -> SomeSing $ sLabelSym l' 