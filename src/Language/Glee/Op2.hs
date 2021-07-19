{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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
             ScopedTypeVariables, TypeApplications, TemplateHaskell #-}
             
module Language.Glee.Op2 where

import Language.Glee.Token 
import Language.Glee.Exp 
import Language.Glee.Hasochism
import Language.Glee.Type
import Data.Singletons.Decide
import Data.Kind (Type)
import Data.Singletons.CustomStar (Sing)
import Data.Constraint
import Language.Glee.Ascii
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Tuple



-- orphan instances. shouldn't matter. exp is too hard to manage w/ all this crap there

instance Eq (BinOpE t) where 
  be1 == be2 = demoteOp2 be1 == demoteOp2 be2 

instance Eq (Some BinOpE) where 
  (Some be1) == (Some be2) = (demoteOp2 be1) == (demoteOp2 be2)

instance IsBinaryOp 'PlusOp NatTy NatTy NatTy where 
  evalBinOp (NatVal n1) PlusE (NatVal n2) = NatVal (n1 + n2)

instance IsBinaryOp 'MinusOp NatTy NatTy NatTy where 
  evalBinOp (NatVal n1) MinusE (NatVal n2) = NatVal (n1 - n2)

instance IsBinaryOp 'TimesOp NatTy NatTy NatTy where 
  evalBinOp (NatVal n1) TimesE (NatVal n2) = NatVal (n1 * n2)

instance IsBinaryOp 'DivideOp NatTy NatTy NatTy where 
  evalBinOp (NatVal n1) DivideE (NatVal n2) = NatVal (n1 `div` n2)

instance IsBinaryOp 'ModOp NatTy NatTy NatTy where 
  evalBinOp (NatVal n1) ModE (NatVal n2) = NatVal (n1 `mod` n2)

instance IsBinaryOp 'LessOp NatTy NatTy BoolTy where 
  evalBinOp (NatVal n1) LessE_ (NatVal n2) = BoolVal (n1 < n2)
 
instance IsBinaryOp 'LessEqOp NatTy NatTy BoolTy where 
  evalBinOp (NatVal n1) LessEQE (NatVal n2) = BoolVal (n1 <= n2)

instance IsBinaryOp 'GreaterOp NatTy NatTy BoolTy where 
  evalBinOp (NatVal n1) GreaterE_ (NatVal n2) = BoolVal (n1 > n2)

instance IsBinaryOp 'GreaterEqOp NatTy NatTy BoolTy where 
  evalBinOp (NatVal n1) GreaterEQE (NatVal n2) = BoolVal (n1 >= n2)

instance IsBinaryOp 'AndOp BoolTy BoolTy BoolTy where 
  evalBinOp (BoolVal b1) AndE (BoolVal b2) = BoolVal (b1 && b2)

instance IsBinaryOp 'OrOp BoolTy BoolTy BoolTy where 
  evalBinOp (BoolVal b1) OrE (BoolVal b2) = BoolVal (b1 || b2)

instance (GlamVal a) => IsBinaryOp 'AppendOp (ListTy a) (ListTy a) (ListTy a) where 
  evalBinOp (ListVal l1) AppendE (ListVal l2) = ListVal (l1 <> l2)

instance GlamVal b => IsBinaryOp 'MapOp (a :-> b) (ListTy a) (ListTy b) where 
  evalBinOp lam@(LamVal body) MapE (ListVal a) = ListVal $ map (\v ->  apply lam  v) a  

instance GlamVal a => IsBinaryOp 'EqOp a a BoolTy where 
  evalBinOp e1 EqE e2 = BoolVal (eqExp (val e1) (val e2))


checkBinOp :: BinOpE op 
           -> STy t1 
           -> Exp ctx t1
           -> STy t2 
           -> Exp ctx t2
           -> (forall res. IsBinaryOp op t1 t2 res => (STy res ,Exp ctx res) -> b )
           ->  b 
checkBinOp b t1 e1 t2 e2 f = case b of 
  PlusE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $  (SNatTy,BinaryOp e1 b e2) 
    _ -> error "boom"

  MinusE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SNatTy,BinaryOp e1 b e2) 
    _ -> error "boom"

  TimesE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SNatTy,BinaryOp e1 b e2) 
    _ -> error "boom"

  DivideE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SNatTy,BinaryOp e1 b e2) 
    _ -> error "boom"

  ModE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SNatTy,BinaryOp e1 b e2) 

  LessE_ -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SBoolTy,BinaryOp e1 b e2)  
    _ -> error "boom"

  LessEQE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $  (SBoolTy,BinaryOp e1 b e2)  
    _ -> error "boom" 

  GreaterE_ -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $ (SBoolTy,BinaryOp e1 b e2)  
    _ -> error "boom"

  GreaterEQE -> case (t1,t2) of 
    (SNatTy,SNatTy) ->  f $  (SBoolTy,BinaryOp e1 b e2)   
    _ -> error "boom"

  AndE -> case (t1,t2) of 
    (SBoolTy,SBoolTy) ->  f $  (SBoolTy,BinaryOp e1 b e2)   
    _ -> error "boom"  

  OrE -> case (t1,t2) of 
    (SBoolTy,SBoolTy) ->  f $  (SBoolTy,BinaryOp e1 b e2)  
    _ -> error "boom"   

  AppendE -> case (t1,t2) of 
    (SListTy x,SListTy y) -> case eqSTy t1 t2 of 
      Nothing -> error "boom0"
      Just Refl -> case (mkGlamWit x,mkGlamWit  y) of 
        (Just GlamWit, Just GlamWit) -> f (SListTy x, BinaryOp e1 AppendE e2)
        _ -> error "boom1"
    _ -> error "boom2"    

  MapE -> case (t1,t2) of 
    (arg :%-> res,SListTy y) -> case eqSTy arg y of 
      Just Refl ->  case mkGlamWit res of 
        Just GlamWit -> f $ (SListTy res,BinaryOp e1 b e2)
        _ -> error "boom"
    _ -> error "boom" 

  EqE -> case eqSTy t1 t2 of 
    Just Refl ->  case mkGlamWit t1 of 
      Just GlamWit -> f $ (SBoolTy,BinaryOp e1 b e2)
      _             -> error "boom"
    _ -> error "boom" 


data GlamWit :: Ty -> Type where 
  GlamWit :: GlamVal t =>  GlamWit  t


mkGlamDict :: forall (t :: Ty). Sing t -> Maybe (Dict (GlamVal t))
mkGlamDict t = case t of 
  (a :%-> b) -> Just Dict

  SNatTy  -> Just Dict 

  SBoolTy -> Just Dict

  SListTy t' -> case mkGlamDict t' of 
    Just Dict -> Just Dict 
    Nothing   -> Nothing

  SRecTy fs -> case mkAllValDict fs of 
    Just Dict -> Just Dict 
    Nothing   -> Nothing

  SVariantTy vs -> case mkAllValDict vs of 
    Just Dict -> Just Dict 
    Nothing -> Nothing 

mkAllValDict :: forall (fs :: [(Label,Ty)])
    . Sing fs -> Maybe (Dict (AllValFields fs))
mkAllValDict fs = case fs of 
  SNil -> Just Dict 
  SCons (STuple2 l tx) xs -> case mkGlamDict tx of 
    Nothing -> Nothing 
    Just Dict -> case mkAllValDict xs of 
      Just Dict -> Just Dict
      Nothing   -> Nothing   


mkGlamWit :: forall (t :: Ty). Sing t -> Maybe (GlamWit t) 
mkGlamWit t = case mkGlamDict t of 
  Just d -> withDict d $ Just $ GlamWit
  Nothing -> Nothing  