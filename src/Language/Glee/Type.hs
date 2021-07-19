{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds,
             GADTs, RankNTypes, FlexibleInstances, OverloadedStrings, TemplateHaskell #-}


module Language.Glee.Type where


import Text.PrettyPrint.ANSI.Leijen
import Data.Text
import Language.Glee.Nat
import Control.Lens.TH ( makeLenses ) 
import Data.Singletons 
import Data.Singletons.Decide 
import Data.Singletons.TH 
import Language.Glee.Ascii 
import qualified Data.Singletons.Prelude.List as SL 
import Data.List as List 
import qualified Data.Map as M 
import Data.Kind (Constraint, Type)
import Language.Glee.Util 
import Data.Constraint
import  Data.Singletons.Prelude 

type a := b = (a,b)

$(singletons [d| 
  data Ty
    =  Ty :-> Ty    -- ^ A function type
    | ListTy Ty 
    | NatTy
    | BoolTy
    | RecTy [(DString,Ty)] 
    | VariantTy [(DString,Ty)] 
    deriving Eq
 |])

infixr 1 :->


-- | Perhaps convert a string representation of a base type into a 'Ty'
readTyCon :: Text -> Maybe Ty
readTyCon "Nat"  = Just NatTy
readTyCon "Bool" = Just BoolTy
readTyCon _      = Nothing

type SCtx (tys :: [Ty]) = Sing tys 

-- | The singleton for the empty context
emptyContext :: SCtx '[]
emptyContext = SNil

-- | Convert a 'Ty' into an 'STy'.
refineTy :: Ty -> (forall ty. STy ty -> r) -> r
refineTy (ty1 :-> ty2) k
  = refineTy  ty1 $ \sty1 ->
    refineTy  ty2 $ \sty2 ->
    k (sty1 :%-> sty2)

refineTy NatTy  k = k SNatTy

refineTy BoolTy k = k SBoolTy

refineTy (ListTy t) k = refineTy t $ \sty1 -> k (SListTy sty1)


refineTy (RecTy xs) k 
  = case go xs of 
        SomeSing sFields -> k (SRecTy sFields)
 where 
   go :: [(Label,Ty)] -> SomeSing [(DString,Ty)]
   go [] = SomeSing SL.SNil
   go ((l,f):xs) = case toSing l of 
     SomeSing sLabel -> case toSing f of 
       SomeSing sFieldTy -> case go xs of 
         SomeSing rest -> SomeSing $ STuple2 sLabel sFieldTy `SL.SCons` rest  

refineTy (VariantTy xs) k 
  = case go xs of 
        SomeSing sFields -> k (SVariantTy sFields)
 where 
   go :: [(Label,Ty)] -> SomeSing [(DString,Ty)]
   go [] = SomeSing SL.SNil
   go ((l,f):xs) = case toSing l of 
     SomeSing sLabel -> case toSing f of 
       SomeSing sFieldTy -> case go xs of 
         SomeSing rest -> SomeSing $ STuple2 sLabel sFieldTy `SL.SCons` rest       

-- | Convert an 'STy' into a 'Ty'
unrefineTy :: STy ty -> Ty
unrefineTy (arg :%-> res)  = unrefineTy arg :-> unrefineTy res

unrefineTy SNatTy            = NatTy

unrefineTy SBoolTy           = BoolTy

unrefineTy (SListTy  t)      = ListTy (unrefineTy t)

unrefineTy (SRecTy  sFields) = RecTy (fromSing sFields)

unrefineTy (SVariantTy sFields) = VariantTy (fromSing sFields)
 
-- | Compare two 'STy's for equality.
eqSTy :: STy ty1 -> STy ty2 -> Maybe (ty1 :~: ty2)
eqSTy (s1 :%->  t1) (s2 :%->  t2)
  | Just Refl <- s1 `eqSTy` s2
  , Just Refl <- t1 `eqSTy` t2
  = Just Refl

eqSTy SNatTy  SNatTy  = Just Refl

eqSTy SBoolTy SBoolTy = Just Refl

eqSTy (SListTy t1) (SListTy t2) = case eqSTy t1 t2 of 
  Just Refl -> Just Refl   
  Nothing -> Nothing

eqSTy t1 t2 = decideEquality t1 t2


-----------------------------------------
-- Pretty-printing

instance Pretty Ty where
  pretty = prettyTy topPrec

instance Show Ty where
  show = render . pretty

instance Pretty (STy ty) where
  pretty = pretty . unrefineTy

arrowLeftPrec, arrowRightPrec, arrowPrec :: Prec
arrowLeftPrec  = 5
arrowRightPrec = 4.9
arrowPrec      = 5 

prettyTy :: Prec -> Ty -> Doc
prettyTy prec (arg :-> res) = maybeParens (prec >= arrowPrec) $
                               hsep [ prettyTy arrowLeftPrec arg
                                    , text "->"
                                    , prettyTy arrowRightPrec res ]

prettyTy _ NatTy  = text "Nat"

prettyTy _ BoolTy = text "Bool"

prettyTy x (ListTy t) = char '[' <> prettyTy x t <> char ']'


prettyTy x (RecTy []) = text "{}" 

prettyTy x (RecTy fs) = char '{' 
                         <+> go fs 
                         <+> char '}' 
  where 
    go :: [(Label,Ty)] -> Doc 
    go [] = text ""
    go xs = hcat . List.intersperse (char ',') 
          $ Prelude.map (\(fl,f) -> text (toString fl) 
                                 <> char ':' 
                                 <+> prettyTy x f) xs 

prettyTy x (VariantTy fs) = char '(' 
                          <+> go fs 
                          <+> char ')'
  where 
    go :: [(Label,Ty)] -> Doc 
    go [] = text ""
    go xs = hcat . List.intersperse (text "|")
          $ Prelude.map (\(fl,f) -> text (toString fl)
                                 <+> char ':' 
                                 <+> prettyTy x f) xs 

