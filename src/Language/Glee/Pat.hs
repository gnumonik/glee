{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell #-}
{-# OPTIONS -Wall #-} 
module Language.Glee.Pat where


import Language.Glee.Ascii 
import Language.Glee.Nat 
import Data.Singletons.TH 
import Language.Glee.Type 
import Language.Glee.Hasochism 
-- naming convention similar to the template haskell ast 
import Data.Constraint 
import Data.Kind
import Data.Singletons.Prelude.List hiding (All)
import Data.Singletons.Decide
import Data.Singletons.Prelude.Maybe


$(singletons[d| 
  data Pat 
    = VarP DString 
    | ConP DString Pat -- for variants  
    | RecP [(DString,Pat)]
    | NatP Nat 
    | BoolP Bool 
    | WildP deriving Show 
  |])

-----
----- Primitive Constraint Manipulation Classes 
-----

type NotEmpty :: [k] -> Constraint 
type family NotEmpty xs where 
  NotEmpty (x ': xs) = ()

type FirstEl :: k -> [k] -> Constraint 
class FirstEl x xs 

instance FirstEl x (x ': xs) 

type FlipC :: (k1 -> k2 -> Constraint) -> k2 -> k1 -> Constraint 
class FlipC c k2 k1 

instance c k1 k2 => FlipC c k2 k1   

flipDict :: Dict (c k1 k2) -> Dict (FlipC c k2 k1)
flipDict Dict = Dict 


-- "Folds" constraint over a typelevel list 
type All :: (k -> Constraint) -> [k] -> Constraint 
class All (c :: k -> Constraint) (xs :: [k]) where 

instance (c x) => All c '[x]
instance All c xs 

data AllC :: (k -> Constraint) -> [k] -> Type where 
  AllZ :: Dict (c a) ->  AllC c (a ': '[])
  AllS :: Dict (c x) -> AllC c xs -> AllC c (x ': xs) 

decideAll :: forall k (c :: k -> Constraint) (xs :: [k])
           . (forall (a :: k). Sing a -> Maybe (Dict (c a)))
          -> Sing xs 
          -> Maybe (AllC c xs)
decideAll p xs = case xs of 
  SNil -> Nothing 
  SCons x SNil -> case p x of 
    Just Dict -> Just $ AllZ Dict 
    Nothing -> Nothing 
  SCons y ys -> case p y of 
    Nothing -> Nothing 
    Just Dict -> case decideAll p ys of 
      Just aw -> Just $ AllS Dict aw
      Nothing -> Nothing 

liftCAll :: forall c xs. AllC c xs -> Dict (All' c xs)
liftCAll aw = case aw of 
  AllZ d -> withDict d Dict 
  (AllS d aw') -> case liftCAll aw' of 
    Dict -> withDict d Dict  


type family All' (c :: k -> Constraint) (xs :: [k]) :: Constraint where 
  All' c '[] = () 
  All' c (x ': xs) = (c x, All' c xs)

elC' :: forall c x xs. (All' c xs) => Ele x xs -> Dict (c x)
elC' e = case e of 
  ElZ -> Dict 
  ElS e' -> elC' e' 

elC :: forall c x xs. (All' c xs, El x xs) => Dict (c x)
elC = case el (Proxy @x) (Proxy @xs) of 
  ElZ -> Dict 
  ElS e' -> elC' e' 

elC'' :: forall c x xs. Dict (All' c xs, El x xs) ->  Dict (c x)
elC'' Dict = elC @c @x @xs 

allImplC :: forall c x xs. (All' c xs, El x xs) :- c x
allImplC = unmapDict elC''

class HFC' l t fs n 
instance HasFieldC' n l t fs => HFC' l t fs n  

instance El x xs :=> El x (y ': xs) where 
  ins = Sub Dict  

-- Witness that a type is a member of a typelevel list 
data Ele :: k -> [k] -> Type where 
  ElZ :: Ele k (k ': ks) 
  ElS :: Ele k ks  -> Ele k (k' ': ks) 

-- produce an El instance dictionary given a witness 
mkElDict :: Ele x xs -> Dict (El x xs)
mkElDict ele' = case ele' of 
  ElZ -> Dict 
  ElS ele'' -> case mkElDict ele'' of 
    Dict -> Dict  

-- produce an el witness on the condition the kind of the list is an instance of SDecide 
ele :: forall k (a :: k) (as :: [k]). SDecide k => Sing a -> Sing as -> Maybe (Ele a as)
ele a as = case as of 
  SNil -> Nothing 
  SCons a' as' -> case decideEquality a a' of 
    Just Refl -> Just ElZ
    Nothing -> case ele a as' of 
      Just e -> Just $ ElS e 
      Nothing -> Nothing  

-- El: Class constaint where the first argument is an element of the second argument 
type El ::  k -> [k] -> Constraint 
class El x xs where 
  el :: proxy1 x -> proxy2 xs -> Ele x xs 

  
instance {-# INCOHERENT #-} El x (x ': xs) where 
  el _ _ = ElZ 
  
instance {-# OVERLAPPABLE #-} El x xs => El x (y ': xs) where 
  el _ _ = ElS $ el (Proxy @x) (Proxy @xs)




-- Constraint that two type level lists each have the same number of elements 
type SameShape :: [j] -> [k] -> Constraint 
class SameShape xs ys 
instance SameShape '[] '[]
instance SameShape xs ys => SameShape (x ': xs) (y ': ys)


-- Zip a list of constraints with a typelevel list of arguments to the constraint 
class ZipC (cs :: [k -> Constraint]) (xs :: [k])

instance ZipC '[] '[]

instance ( SameShape cs xs
         , ZipC cs xs
         , KindOf c ~ (k -> Constraint)
         , KindOf x ~ k
         , c x) => ZipC (c ': cs) (x ': xs)

-- ZipWith for two argument constraitns 
type ZipCWith :: [j] -> [k] -> (j -> k -> Constraint) -> Constraint 
class ZipCWith js ks cs 

instance ZipCWith '[] '[] c 

instance ( SameShape js ks
         , ZipCWith js ks c 
         , KindOf j' ~ j
         , KindOf k' ~ k 
         , c j' k') => ZipCWith (j' ': js) (k' ': ks) c 


class MatchPatTy (p :: Pat) (t :: Ty) 

class MatchFieldPat (p :: (Label,Pat)) (f :: (Label,Ty))

instance MatchPatTy p t => MatchFieldPat '(l,p) '(l,t)

instance (HasFieldC l t fs,MatchPatTy p t, LookupType l fs ~ 'Just t) 
          => MatchPatTy ('ConP l p) ('VariantTy fs) 

instance (ZipCWith ps fs MatchFieldPat) => MatchPatTy ('RecP ps) ('RecTy fs)

instance MatchPatTy ('NatP n) 'NatTy

instance MatchPatTy ('BoolP b) 'BoolTy

instance MatchPatTy 'WildP _a 

instance MatchPatTy ('VarP l) _a 

data MatchBox :: Pat -> Ty -> Type where 
  MatchBox :: MatchPatTy p t => MatchBox p t 

matchDict :: forall p t. MatchBox p t -> Dict (MatchPatTy p t)
matchDict MatchBox = Dict 


testMatch :: SPat p -> STy t -> Maybe (Dict (MatchPatTy p t))
testMatch p t = matchDict <$> mkMatchBox p t 

mkMatchBox :: forall p t. Sing (p :: Pat) -> Sing (t :: Ty) -> Maybe (MatchBox p t)
mkMatchBox p t = case (p,t) of 
  (SVarP _, _) -> Just MatchBox
  (SWildP, _)  -> Just MatchBox 
  (SNatP _, SNatTy)           -> Just MatchBox 
  (SBoolP _, SBoolTy)         -> Just MatchBox 
  (SConP l p', SVariantTy fs) -> mkConPBox (SConP l p') (SVariantTy fs)
  (SRecP fps, SRecTy rs)      -> mkRecPBox (SRecP fps) (SRecTy rs)
  _ -> Nothing 
 where 
   mkConPBox :: forall l p' fs. Sing ('ConP l p') 
             -> Sing ('VariantTy fs)
             -> Maybe (MatchBox ('ConP l p') ('VariantTy fs) )
   mkConPBox (SConP l p') (SVariantTy fs) = go (sLookupType l fs) 
    where 
      go ::  Sing (LookupType l fs) -> Maybe (MatchBox ('ConP l p') ('VariantTy fs) )
      go st = case st of 
        SNothing -> Nothing 
        SJust tx -> case decideHasField fs l tx of 
          Nothing -> Nothing 
          Just hf -> case proveHasFieldC hf of 
            d -> case mkMatchBox p' tx  of 
              Just md -> Just $ withDict d $ withDict (matchDict md)  MatchBox 
              Nothing -> Nothing 

   mkRecPBox :: forall fps rs
              . Sing ('RecP fps) 
             -> Sing ('RecTy rs) 
             -> Maybe (MatchBox ('RecP fps) ('RecTy rs) )
   mkRecPBox (SRecP fps) (SRecTy rs) = case mkShapeWit fps rs of 
     Nothing -> Nothing 
     Just shapeDict -> case withDict shapeDict $ mkZipWit fps rs of 
      Just Dict -> Just MatchBox 
      Nothing -> Nothing 
    where 
      mkZipWit :: forall (ps :: [(Label,Pat)]) (rs' :: [(Label,Ty)])
                . SameShape ps rs' => Sing ps -> Sing rs' -> Maybe (Dict (ZipCWith ps rs' MatchFieldPat))
      mkZipWit ps rs' = case (ps,rs') of 
          (SNil,SNil) -> Just Dict  
          (SCons x xs, SCons y ys) -> case mkFieldWit x y of
            Nothing -> Nothing 
            Just Dict -> case mkShapeWit xs ys of 
              Nothing -> Nothing 
              Just Dict -> case mkZipWit xs ys of 
                Just Dict -> Just Dict 
                Nothing -> Nothing
          _ -> Nothing 

      mkFieldWit :: forall (fp :: (Label,Pat)) (f :: (Label,Ty))
                  . Sing fp -> Sing f -> Maybe (Dict (MatchFieldPat fp f))
      mkFieldWit (STuple2 pl pp) (STuple2 fl ft) = case decideEquality pl fl of
        Nothing -> Nothing  
        Just Refl -> case matchDict <$> mkMatchBox pp ft of 
          Just Dict -> Just Dict 
          Nothing -> Nothing  

      mkShapeWit :: forall k1 k2 (xs :: [k1]) (ys :: [k2])
                  . Sing xs -> Sing ys -> Maybe (Dict (SameShape xs ys))
      mkShapeWit xs ys = case (xs, ys) of 
        (SNil,SNil) -> Just Dict
        (SCons _ us, SCons _ ws) -> case mkShapeWit us ws of 
          Just Dict -> Just Dict 
          Nothing -> Nothing  
        _ -> Nothing 



elDict :: forall k (x :: k) (xs :: [k]). (SDecide k) 
       => Sing x -> Sing xs -> Maybe (Dict (El x xs))
elDict x xs = case ele x xs of 
  Just e -> Just $ mkElDict e
  Nothing -> Nothing  

type (<++>) :: [k] -> [k] -> [k]
type family (<++>) xs ys where 
  (<++>) (x ': xs) '[] = (x ': xs) 
  (<++>) '[] (y ': ys) = (y ': ys)
  (<++>) '[] '[] = '[] 
  (<++>) (x ': xs) ys = x ': (xs <++> ys)


(%<++>) :: forall k (xs :: [k]) (ys :: [k])
         . Sing xs -> Sing ys -> Sing (xs <++> ys)
xs %<++> ys = case (xs,ys) of 
  (xs'@(SCons _ _),SNil) -> xs'
  (SNil,ys'@(SCons _ _)) -> ys'
  (SNil,SNil) -> SNil
  (SCons x' xs', ys'@(SCons _ _)) -> x' `SCons` (xs' %<++> ys')


type Guard :: Pat -> Ty -> [Ty]
type family Guard p t where 
  Guard ('VarP _l) t = (t ': '[])

  Guard 'WildP _t    = '[]

  Guard ('ConP l p) ('VariantTy vs) 
    = GoConP ('ConP l p) vs

  Guard ('RecP fps) ('RecTy fs) = FieldGuards fps fs  

  Guard ('NatP n) 'NatTy   = '[]

  Guard ('BoolP b) 'BoolTy = '[] 

type GoConP :: Pat -> [(Label,Ty)] -> [Ty]
type family GoConP p vs where 
  GoConP ('ConP l p) ( '(l',t) ': vs) = If (l == l') (Guard p t) (GoConP ('ConP l p) vs)

type FieldGuards :: [(Label,Pat)] -> [(Label,Ty)] -> [Ty]
type family FieldGuards fps fs where
  FieldGuards '[] '[] = '[] 
  FieldGuards ( '(l,p) ': fps) ( '(l',t) ': fs) 
    = If (l == l') 
         (Guard p t <++> FieldGuards fps fs)
         '[]


mkGuards :: Sing (p :: Pat) -> Sing (t :: Ty) -> Maybe (Sing (Guard p t) )
mkGuards p t = case (p,t) of 
  (SVarP _,t') -> Just (SCons t' SNil)

  (SWildP,_)  -> Just SNil 

  (SConP l p', SVariantTy w@(SCons (STuple2 l' t') vs)) -> 
     case l %== l' of 
        STrue -> mkGuards p' t' 
        SFalse ->     case lookupFType vs l of 
          Nothing -> error $ (toString . fromSing $ l) 
                       <> " is not a constructor of " 
                       <> (show . fromSing $ w) 
          Just _  ->    mkGuards (SConP l p') (SVariantTy vs)

  (SRecP fps, SRecTy fs) -> mkFieldGuards fps fs 

  (SNatP _n, SNatTy) -> Just SNil 

  (SBoolP _b, SBoolTy) -> Just SNil 

  _ -> Nothing 

mkFieldGuards :: Sing (fps :: [(Label,Pat)]) 
              -> Sing (fs :: [(Label,Ty)]) 
              -> Maybe (Sing (FieldGuards fps fs))
mkFieldGuards fps fs = case (fps, fs) of 
  (SNil,SNil) -> Just SNil 
  (SCons (STuple2 l p) fps', SCons (STuple2 l' t) fs') -> case mkGuards p t of 
    Just sGuards -> case l %== l' of 
      STrue -> (sGuards %<++>) <$> mkFieldGuards fps' fs'
      SFalse -> Nothing  
    Nothing -> Nothing 

  _ -> Nothing 

nopeLabel :: Sing ('DString '[ 'DChar '( 'Upper, 'N_)
                             , 'DChar '( 'Lower, 'O_)
                             , 'DChar '( 'Lower, 'P_)
                             , 'DChar '( 'Lower, 'E_)])
nopeLabel = sing 

okLabel :: Sing ('DString '[ 'DChar '( 'Upper, 'O_)
                           , 'DChar '( 'Lower, 'K_)])
okLabel = sing 

testST :: STy
  ('VariantTy
     '[ '( 'DString '[ 'DChar '( 'Upper, 'O_), 'DChar '( 'Lower, 'K_)],
           'NatTy),
        '( 'DString
             '[ 'DChar '( 'Upper, 'N_), 'DChar '( 'Lower, 'O_),
                'DChar '( 'Lower, 'P_), 'DChar '( 'Lower, 'E_)],
           'RecTy '[])])
testST = SVariantTy 
       $ STuple2 okLabel SNatTy
 `SCons` STuple2 nopeLabel (SRecTy SNil)
 `SCons` SNil 

testPat :: SPat
  ('ConP
     ('DString
        '[ 'DChar '( 'Upper, 'N_), 'DChar '( 'Lower, 'O_),
           'DChar '( 'Lower, 'P_), 'DChar '( 'Lower, 'E_)])
     ('RecP '[]))
testPat = SConP nopeLabel (SRecP SNil)

