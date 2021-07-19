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


module Language.Glee.Hasochism where

import Language.Glee.Ascii 
import Language.Glee.Type 
import Data.Constraint
import Data.Kind (Type)
import Language.Glee.Nat
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import qualified Data.Map as M
import Language.Glee.Util
import Control.Lens.TH (makeLenses)
import Data.Functor.Identity


{-- Typeclass stuff. Has to go here until module reshuffling --}

data HasField :: Label -> Ty -> [(Label,Ty)] -> Type where 
  FHere :: HasField x y ( '(x,y) ': zs )
  FThere :: HasField x y zs -> HasField x y (z ': zs)

proveHasFieldC ::  HasField l t fs -> Dict (HasFieldC l t fs)
proveHasFieldC hf = case hf of 
  FHere -> Dict 
  FThere hf' -> case proveHasFieldC hf' of 
    Dict -> Dict  


class  HasFieldC (x :: Label) (y :: Ty) (zs :: [(Label,Ty)]) where 
  hasField ::  proxy1 x -> proxy2 y -> proxy3 zs -> HasField x y zs 

instance    HasFieldC x y ( '(x,y) ': zs) where 
  hasField _ _ _ = FHere 

-- absolutely no idea whether INCOHERENT is what i really want here 
instance  {-# INCOHERENT #-}  HasFieldC x y zs => HasFieldC x y (z ': zs) where 
  hasField _ _ _ = FThere $ hasField (Proxy @x) (Proxy @y) (Proxy @zs)

class FirstRec' x y zs  n 
       => HasFieldC' (n :: Nat) (x :: Label) (y :: Ty) (zs :: [(Label,Ty)]) where 
            hasField'  :: proxy n -> proxy1 x -> proxy2 y -> proxy3 zs -> HasField x y zs 

instance   HasFieldC' 'Z x y ( ( '(x,y) ': zs)) where 
  hasField' _ _ _ _ = FHere 

instance  (HasFieldC' n x y zs, FirstRec' x y ( w ': zs)  ('S n))
         => HasFieldC' ('S n) x y (w ': zs) where 
           hasField' prox a b c = case pos @x @y @zs @n of 
             SingInstance -> FThere (hasField' (sing @n) (Proxy @x) (Proxy @y) (Proxy @zs))

type FirstRec ::  Label -> Ty -> [(Label,Ty)] -> Nat 
type family FirstRec (x :: Label) (y :: Ty) (zs :: [(Label,Ty)]) where 
  FirstRec x y ( '(x,y) ': zs) = Z 
  FirstRec x y ( w ': zs) = 'S (FirstRec x y zs)


type FirstRec' :: Label -> Ty -> [(Label,Ty)] -> Nat -> Constraint 
class FirstRec' l t fs n where 
  pos :: SingInstance n 

data HasFieldBox :: Label -> Ty -> [(Label,Ty)] -> Nat -> Type where 
  HasFieldBox :: (HasFieldC' n l t fs) 
              => Sing n 
              -> Dict (HasFieldC' n l t fs)
              -> HasField l t fs 
              -> HasFieldBox l t fs n 

sDict :: Dict (HasFieldC' n l t fs) -> Dict (HasFieldC' ('S n) l t (x ': fs))
sDict Dict = Dict 

type LookupType :: Label -> [(Label,Ty)] -> Maybe Ty 
type family LookupType l fs where 
  LookupType l '[] = Nothing 
  LookupType l ( '(l',t) ': fs) = If (l == l') (Just t) (LookupType l fs) 

sLookupType :: Sing l -> Sing fs -> Sing (LookupType l fs)
sLookupType l fs = case fs of 
  SNil -> SNothing 
  SCons (STuple2 l' t) fs' -> case  (l %== l') of 
    STrue -> (SJust t) 
    SFalse -> (sLookupType l fs') 


decideHasField :: forall (xs :: [(Label,Ty)]) (l :: Label) (t :: Ty)
                . Sing xs -> Sing l -> Sing t -> Maybe (HasField l t xs)
decideHasField fields label ty = case fields of 
  SNil -> Nothing
  SCons (STuple2 l v) xs -> case label %~ l of 
    Disproved void -> case decideHasField xs label ty of 
      Just hf -> Just . FThere $ hf 
      Nothing -> Nothing 
    Proved Refl -> case v %~ ty of 
      Proved Refl -> Just FHere     
      Disproved void -> case decideHasField xs label ty of 
        Just hf -> Just . FThere $ hf 
        Nothing -> Nothing 
      
mkFieldBox :: forall (l::Label) (t::Ty) (fs::[(Label,Ty)])
            . HasField l t fs -> Some (HasFieldBox l t fs)
mkFieldBox hf = case hf of 
  FHere -> Some $ HasFieldBox SZ Dict FHere 
  FThere hf' -> case mkFieldBox hf' of 
    Some x -> case x of 
      bx@(HasFieldBox n d hx) ->  Some $ HasFieldBox (SS n) Dict (FThere hx)   
----------------------------------------------------


instance (FirstRec l t fs ~ 'Z) => FirstRec' l t fs 'Z where 
  pos = withSingI SZ SingInstance 

instance (FirstRec' l t fs n ) => FirstRec' l t (x ': fs) ('S n) where 
  pos  = case (pos @l @t @fs @n) of 
    SingInstance -> withSingI (SS $ sing @n) SingInstance 

data Some :: (k -> Type) ->  Type where 
  Some :: forall k (a :: k) (c :: k -> Type)
        . c a -> Some c 

------------------
---- Some utility types/functions that are here for staging reasons
------------------

data ConstructorInfo  ::   Label ->Type where 
  MkConstructor :: ( ValidDataCon l
                   , HasFieldC l ty vs)
                =>  Sing l 
                -> Sing (ty :: Ty)
                -> Sing ('VariantTy vs)
                -> ConstructorInfo l

data Some2 :: (k -> j -> Type) -> Type where 
  Some2 :: forall k j(a :: k) (b :: j) (c :: k -> j -> Type)
         . c a b -> Some2 c 


data TySyn :: Label -> Ty -> Type where 
  MkTySyn :: Sing (l :: Label)
          -> Sing (ty :: Ty)
          -> TySyn l ty 

mkConstructor :: Label -> Ty -> [(Label,Ty)] -> Maybe (Some ConstructorInfo)
mkConstructor l t vs =  
    case  toSing l of 
    SomeSing l' -> case toSing t of 
      SomeSing t' -> case toSing vs of 
        SomeSing vs' -> case isValidDataCon l' of
          Nothing -> Nothing  
          Just dConDict -> case decideHasField vs' l' t'  of 
            Nothing -> Nothing 
            Just hf ->case proveHasFieldC hf of 
              hfDict -> 
                withDict dConDict $
                withDict hfDict $  
                  Just . Some $ MkConstructor  l' t' (SVariantTy vs') 


mkConstructor' :: (ValidDataCon l, HasFieldC l t vs) 
                  => Sing (l :: Label)
                  -> Sing (t :: Ty)
                  -> Sing (vs :: [(Label,Ty)])
                  -> ConstructorInfo l
mkConstructor' l t vs = MkConstructor l t (SVariantTy vs) 

-- the cInfo doesn't strictly need to be existentialized but i don't feel like writing 
-- more hList functions atm 
mkConstructors :: Sing (VariantTy fs) -> Maybe [Some ConstructorInfo]
mkConstructors (SVariantTy fs) = go fs 
  where 
    go :: forall vs
        . Sing (vs :: [(Label,Ty)])
       -> Maybe [Some ConstructorInfo]
    go SNil = Just []
    go (SCons (STuple2 l t) vs) = case isValidDataCon l of 
        Nothing -> Nothing 
        Just Dict ->  case proveHasFieldC <$> decideHasField fs l t of 
          Nothing -> Nothing 
          Just Dict -> (Some (MkConstructor l t (SVariantTy fs)) :) <$> go vs 
          
           
data Context = Context { _types        :: M.Map Label Ty 
                       , _dataCons     :: Some (HList (ConstructorInfo))
                       , _tyCons       :: M.Map Label Ty 
                       , _boundNames   :: [Label]}

unit = SRecTy SNil 

testSumType :: Some (HList ConstructorInfo)
testSumType = runIdentity $ do 
  case toSing $(mkDString "Ok") of 
    SomeSing ok -> case  toSing $(mkDString "Nope") of 
      SomeSing nope -> case (isValidDataCon ok, isValidDataCon nope) of 
        (Just Dict, Just Dict) -> do 
          testVs <- pure $  (STuple2 ok SNatTy) 
                      `SCons` (STuple2 nope (SRecTy SNil))
                      `SCons` SNil 
          okCon <- pure $  mkConstructor' ok SNatTy  testVs
          nopeCon <- pure $  mkConstructor' nope unit testVs 
          case withSingI nope $ hInsert nopeCon HZ of 
            Left _ -> error "testSumType broken!"
            Right hl -> case withSingI ok $ hInsert okCon hl of 
              Left _-> error "boomboom!"
              Right x -> pure $ Some x 
        _ -> error "testSumType broken2"
        

mkVariant :: Some (HList ConstructorInfo) -> Ty 
mkVariant (Some hl) = case hl of 
  HZ -> VariantTy []
  hs@(HS hl' ci) -> case ci of 
    MkConstructor _ _ vs' -> fromSing vs'  

testSum' = mkVariant testSumType 



initContext :: Context
initContext = Context baseTypes testSumType M.empty []
  where 
    baseTypes = M.fromList [ (boolL,BoolTy)
                           , (natL,NatTy)
                           , (testSumL,mkVariant testSumType)]

    boolL = $(mkDString "Bool")  
    natL  = $(mkDString "Nat") 

    testSumL =  $(mkDString "TestSum")  

lookupFType :: forall (xs :: [(Label,Ty)]) (l :: Label)
             . Sing xs -> Sing l -> Maybe (SomeSing Ty)
lookupFType fields label = case fields of 
  SNil -> Nothing 
  SCons (STuple2 l t) xs -> case label %~ l of 
    Proved Refl -> Just $ SomeSing t
    Disproved void -> lookupFType xs label  


type LabelType :: Label -> [(Label,k)] -> Maybe k 
type family LabelType l fs where 
  LabelType l '[] = Nothing 
  LabelType l ( '(l',f) ': fs) = If (l == l') (Just f) (LabelType l fs)

sLabelType :: Sing (l :: Label) -> Sing (fs :: [(Label,Ty)]) -> Sing (LabelType l fs)
sLabelType l fs = case fs of 
  SNil -> SNothing 
  SCons (STuple2 l' t) xs -> case l %== l' of 
    STrue -> SJust t
    SFalse -> sLabelType l xs  



makeLenses ''Context 