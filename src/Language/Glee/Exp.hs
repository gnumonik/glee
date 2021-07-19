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

module Language.Glee.Exp  where

import Language.Glee.Pretty
import Language.Glee.Token
import Language.Glee.Util
import Language.Glee.Type
import Language.Glee.Nat 
import Data.Kind (Constraint, Type)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Data.Singletons 
import qualified Data.Singletons.TH as STH 
import qualified Data.Singletons.Prelude as S 
import Data.Singletons.Decide 
import Data.Singletons.Prelude.Eq (PEq((==)), SEq((%==)))
import Unsafe.Coerce 
import Data.Singletons.Prelude (TrueSym0, PSemigroup(type (<>)) )
import Data.Singletons.Prelude.Monoid
import Data.Constraint 
import Language.Glee.Ascii 
import Language.Glee.Hasochism 
import Language.Glee.Pat 

---- Binary Operation Stuff. Has to go here for staging. See Op2 module for instances/supporting definitions

promoteOp2 :: Op2 -> Some BinOpE
promoteOp2 x =  case x of  
  PlusOp      -> Some PlusE 
  MinusOp     -> Some MinusE 
  TimesOp     -> Some TimesE  
  DivideOp    -> Some DivideE 
  ModOp       -> Some ModE  
  LessOp      -> Some LessE_ 
  LessEqOp    -> Some LessEQE 
  GreaterOp   -> Some GreaterE_ 
  GreaterEqOp -> Some GreaterEQE 
  AndOp       -> Some AndE 
  OrOp        -> Some OrE                                           
  AppendOp    -> Some AppendE                        
  MapOp       -> Some MapE                   
  EqOp        -> Some EqE 

demoteOp2 :: BinOpE t -> Op2 
demoteOp2 b = case b of 
  PlusE      -> PlusOp 
  MinusE     -> MinusOp 
  TimesE     -> TimesOp 
  DivideE    -> DivideOp 
  ModE       -> ModOp 
  LessE_     -> LessOp 
  LessEQE    -> LessEqOp 
  GreaterE_  -> GreaterOp 
  GreaterEQE -> GreaterEqOp 
  AndE       -> AndOp 
  OrE        -> OrOp 
  AppendE    -> AppendOp 
  MapE       -> MapOp 
  EqE        -> EqOp 

data BinOpE :: Op2 -> Type where 
  PlusE       :: BinOpE 'PlusOp 
  MinusE      :: BinOpE 'MinusOp 
  TimesE      :: BinOpE 'TimesOp 
  DivideE     :: BinOpE 'DivideOp 
  ModE        :: BinOpE 'ModOp
  LessE_      :: BinOpE 'LessOp 
  LessEQE     :: BinOpE 'LessEqOp 
  GreaterE_   :: BinOpE 'GreaterOp 
  GreaterEQE  :: BinOpE 'GreaterEqOp  
  AndE        :: BinOpE 'AndOp 
  OrE         :: BinOpE 'OrOp  
  AppendE     :: BinOpE 'AppendOp 
  MapE        :: BinOpE 'MapOp 
  EqE         :: BinOpE 'EqOp 

type IsBinaryOp :: Op2 -> Ty -> Ty -> Ty -> Constraint 
class GlamVal r => IsBinaryOp op arg1 arg2 r where 
 evalBinOp ::  Val arg1 -> BinOpE op -> Val arg2 -> Val r 

data LabelE :: Label -> Type where 
  LabelE :: Sing (l :: Label) -> LabelE l 

-- | @Elem xs x@ is evidence that @x@ is in the list @xs@.
-- @EZ :: Elem xs x@ is evidence that @x@ is the first element of @xs@.
-- @ES ev :: Elem xs x@ is evidence that @x@ is one position later in
-- @xs@ than is indicated in @ev@
data Elem :: [a] -> a -> * where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

-- | Convert an 'Elem' to a proper de Bruijn index
elemToInt :: Elem ctx ty -> Int
elemToInt EZ     = 0
elemToInt (ES e) = 1 + elemToInt e


processMatch :: Sing xs
             -> Exp xs res 
             -> ValList xs
             -> Exp '[] res 
processMatch  g ge vl = case g of 
  S.SNil -> ge 
  g'@(S.SCons x xs) -> loopgo g vl' ge 
  where 
    loopgo :: forall (xs :: [Ty]) (r :: Ty)
            . Sing xs 
           -> ValList' xs 
           -> Exp xs r 
           -> Exp '[] r 
    loopgo si va ex = case si of 
      S.SNil -> ex 
      si'@(S.SCons x xs) -> case go si' va ex of 
        (S.SNil,e,VZ') -> e 
        (sxs,e,vs@VS' {}) -> loopgo sxs vs e 

    go :: forall (x :: Ty) (xs :: [Ty]) (r :: Ty). 
            Sing (x ': xs)
        ->  ValList' (x ': xs)
        ->  Exp (x ': xs) r 
        -> (Sing xs, Exp xs r, ValList' xs)
    go sxs (VS' vs sa va)  e = case vs of 
      VZ' -> (S.SNil,subst va e, VZ') 
      vs'@VS' {} -> case sxs of 
        S.SCons x xs ->   (xs,subst va e, vs')

    vl' = mkValList' vl 

    mkValList' :: forall xs. ValList xs -> ValList' xs 
    mkValList' vx = case vx of 
      VZ -> VZ' 
      VS rest sx ex -> case mkValList' rest of   
        VZ' -> VS' VZ' sx ex 
        ss@(VS' vr sr er) -> vCons' sx ex ss

vCons' :: Sing a -> Exp '[] a -> ValList' ts -> ValList' (a ': ts)
vCons' sa ex vl = case vl of 
  VZ' -> VS' VZ' sa ex 
  vs -> VS' vs sa (vShift ex vs)
 where 
   vShift :: forall r ctx. Exp '[] r -> ValList' ctx -> Exp ctx r 
   vShift ex vl = case vl of 
     VZ' -> ex
     VS' rest sa _ -> case vShift ex rest of 
       blah -> shift blah 

vl'Sings :: ValList' ts -> Sing ts 
vl'Sings VZ' = S.SNil 
vl'Sings (VS' rest s _) = s `S.SCons` vl'Sings rest  

data ValList :: [Ty] -> Type where 
  VZ :: forall . ValList '[]
  VS :: ValList ts ->  Sing a -> Exp '[] a -> ValList  (a ': ts)

data ValList' :: [Ty] -> Type where 
  VZ' :: ValList' '[]
  VS' :: ValList' ts -> Sing a -> Exp ts a -> ValList' (a ': ts)

vlSings :: ValList ts -> Sing ts 
vlSings VZ = S.SNil
vlSings (VS rest sa _) = sa `S.SCons` vlSings rest  

vAppend :: ValList xs -> ValList ys -> ValList (xs <++> ys)
vAppend VZ VZ = VZ 
vAppend vx@VS {} VZ = vx 
vAppend VZ vy@VS {} = vy
vAppend x@(VS restx sx ex) y@(VS resty sy ey) = go x y 
  where 
    go :: forall x xs y ys
        . ValList (x ': xs) 
        -> ValList (y ': ys)
        -> ValList ((x ': xs) <++> (y ': ys))
    go (VS restx sx ex) vy = vCons sx ex (restx `vAppend` vy) 

vCons :: Sing a -> Exp '[] a -> ValList ctx -> ValList (a ': ctx)
vCons  sa ex vl = VS vl sa  ex

data MatchE :: Ty -> Ty -> Pat -> Type where 
  MatchE :: Sing (p :: Pat)
         -> Sing (arg :: Ty)
         -> Sing (res :: Ty)
         -> Sing (Guard p arg)
         -> (ValList (Guard p arg) -> Exp '[] res)
         -> MatchE arg res p 

data Match ::  [Ty] -> Ty -> Pat -> Type where 
  Match :: ( MatchPatTy p arg
           , GlamVal arg)
        => Sing (p :: Pat) 
        -> Sing arg 
        -> Exp ctx (arg :-> res) 
        -> Match ctx (arg :-> res) p

data MatchList :: [Ty]  -> Ty -> Ty -> Type where 
  MZ :: Dict (MatchPatTy p arg)
     -> Sing (Guard p arg) 
     -> Sing p 
     -> Sing arg
     -> Sing res 
     -> Exp (Guard p arg) res
     -> MatchList ctx  arg res

  MS :: MatchList ctx arg res 
     -> Dict (MatchPatTy p arg)
     -> Sing (Guard p arg)
     -> Sing p 
     -> Sing arg 
     -> Sing res 
     -> Exp (Guard p arg) res
     -> MatchList ctx arg res 
 
mlcons :: Dict (MatchPatTy p arg)
       -> Sing (Guard p arg)
       -> Sing p 
       -> Sing arg 
       -> Sing res
       -> Exp (Guard p arg) res
       -> MatchList ctx arg res 
       -> MatchList ctx arg res 
mlcons d w p a r  ex ml = MS ml d w p a r ex 


-- | @Exp ctx ty@ is a well-typed expression of type @ty@ in context
-- @ctx@. Note that a context is a list of types, where a type's index
-- in the list indicates the de Bruijn index of the associated term-level
-- variable.
data Exp :: [Ty] -> Ty -> * where
  Var      :: Elem ctx (ty :: Ty) -> Exp ctx (ty :: Ty)

  Lam      :: Exp (arg ': ctx) res -> Exp ctx (arg :-> res)

  App      :: Exp ctx (arg :-> res) -> Exp ctx arg -> Exp ctx res


  BinaryOp :: IsBinaryOp bOp t1 t2 res 
           => Exp ctx t1 -> BinOpE bOp -> Exp ctx t2 -> Exp ctx res 

  Cond     :: Exp ctx BoolTy -> Exp ctx ty -> Exp ctx ty -> Exp ctx ty

  CaseE ::  Exp ctx arg 
        ->  MatchList ctx arg res 
        ->  Exp ctx res 

  Cons     :: Exp ctx ty -> Exp ctx (ListTy ty) -> Exp ctx (ListTy ty)

  Nil      :: Exp ctx (ListTy ty) -- this is the annoying part 
 -- Fix   :: Exp ctx (ty -> ty) -> Exp ctx ty

  -- this is more or less "Unit"
  RZ       :: Exp ctx (RecTy '[])

  RS       :: SingI (l :: Label) 
           => Exp ctx (RecTy xs)
           -> Exp ctx (t :: Ty)
           -> Exp ctx (RecTy ( '(l,t) ': xs))

  Project  :: ( HasFieldC' n l res fs
              , LabelType l fs ~ Just res)
           =>  Sing n 
           -> Exp ctx (RecTy fs) 
           -> LabelE l 
           -> Exp ctx res  

  DataCon :: (HasFieldC l vty vs
             ,ValidDataCon l)
          => LabelE l 
          -> Sing vty 
          -> Exp ctx vty 
          -> Exp ctx (VariantTy vs)

  NatE  :: Nat -> Exp ctx NatTy

  BoolE :: Bool -> Exp ctx BoolTy


-- | Classifies types that can be values of glee expressions
class GlamVal (t :: Ty) where
  -- | Well-typed closed values. Encoded as a data family with newtype
  -- instances in order to avoid runtime checking of values
  data Val t

  -- | Convert a glee value back into a glee expression
  val :: Val (t :: Ty) -> Exp '[] (t :: Ty)

instance GlamVal NatTy where
  newtype Val NatTy = NatVal Nat 
  val (NatVal n) = NatE n

instance GlamVal BoolTy where
  newtype Val BoolTy = BoolVal Bool
  val (BoolVal b) = BoolE b

instance GlamVal (ListTy a) where 
  newtype Val (ListTy a) = ListVal [Exp '[] a]
  val (ListVal xs) = foldr Cons Nil xs

instance  GlamVal (a :-> b) where
  newtype Val (a :-> b) = LamVal (Exp '[a] b)
  val (LamVal body) = Lam body

instance  GlamVal (RecTy  fs) where 
  newtype Val (RecTy fs) = RecVal (RecValList (RecTy fs))
  val (RecVal rList) = go rList 
    where 
      go :: forall (fs :: [(Label,Ty)])
          . RecValList (RecTy fs) -> Exp '[] (RecTy  fs)
      go RValZ = RZ 
      go (RValS xs l v) = withSingI l $ RS (go xs) v

instance  GlamVal (VariantTy fs) where 
  newtype Val (VariantTy fs) = VVal (VValBox fs)
  val (VVal (VValBox l t v)) = DataCon (LabelE l) t  v

data VValBox :: [(Label,Ty)] -> Type where 
  VValBox :: (HasFieldC l t fs, ValidDataCon l) 
          => Sing l -> Sing t -> Exp '[] t -> VValBox fs 
----------------------------------------------------
-- | Equality on expressions, needed for testing
eqExp :: forall ctx1 ctx2 ty1 ty2. Exp ctx1 ty1 -> Exp ctx2 ty2 -> Bool
eqExp (Var e1)      (Var e2)      = elemToInt e1 == elemToInt e2

eqExp (Lam body1)   (Lam body2)   = body1 `eqExp` body2

eqExp (App e1a e1b) (App e2a e2b) = e1a `eqExp` e2a && e1b `eqExp` e2b
--eqExp (Arith e1a op1 e1b) (Arith e2a op2 e2b)
--  = e1a `eqExp` e2a && op1 `eqArithOp` op2 && e1b `eqExp` e2b
eqExp (Cond e1a e1b e1c) (Cond e2a e2b e2c)
  = e1a `eqExp` e2a && e1b `eqExp` e2b && e1c `eqExp` e2c

eqExp (NatE i1)     (NatE i2)     = i1 == i2

eqExp (BoolE b1)    (BoolE b2)    = b1 == b2

eqExp Nil           Nil           = True

eqExp (Cons e1 e2)  (Cons e3 e4)  = (e1 `eqExp` e3) && (e2 `eqExp` e4)

eqExp (RS rest ex) (RS rest' ex') = eqExp ex ex' && eqExp rest rest' 

eqExp RZ RZ                       = True 

eqExp _             _             = False

instance Eq (Some2 Exp) where 
  Some2 e1 == Some2 e2 = eqExp e1 e2 

----------------------------------------------------
-- Pretty-printing

instance Pretty (Exp ctx ty) where
  pretty = defaultPretty

instance PrettyExp (Exp ctx ty) where
  prettyExp = prettyExpr

instance GlamVal ty => Pretty (Val ty) where
  pretty = defaultPretty

instance GlamVal ty => PrettyExp (Val ty) where
  prettyExp coloring prec v = prettyExpr coloring prec (val v)

instance GlamVal t => PrettyExp [Val t] where 
  prettyExp coloring prec v = pretty $ map (prettyExpr coloring prec . val) v

instance AllValFields fs => PrettyExp (Val (RecTy fs)) where 
  prettyExp coloring prec v = prettyExpr coloring prec (val v)

-- | Pretty-prints a 'Val'. This needs type information to know how to print.
-- Pattern matching gives GHC enough information to be able to find the
-- 'GlamVal' instance needed to construct the 'PrettyExp' instance.
prettyVal :: forall (t :: Ty). Val t -> STy t -> Doc
prettyVal val SNatTy        = pretty val

prettyVal val SBoolTy       = pretty val

prettyVal val (a :%-> b)    = pretty val

prettyVal val (SListTy t)   = case val of 
  ListVal xs -> list $ map pretty xs

prettyVal val (SRecTy fs)   = case val of 
  RecVal v -> char '{' 
           <> prettyRecVal v 
           <> char '}'   
  where 
    prettyRecVal :: forall fs. RecValList (RecTy fs) -> Doc 
    prettyRecVal r  = case r of 
      RValZ -> text ""
      RValS rest l e -> text (toString . fromSing $ l) 
                     <> char ':' 
                     <> pretty e 
                     <> case rest of 
                          RValZ -> char '}'
                          _     -> char ',' <+> prettyRecVal rest  
prettyVal val (SVariantTy vs) = case val of 
  VVal (VValBox l t ex) -> text (toString . fromSing $ l) 
                      <> case ex of 
                          RZ -> text ""
                          _  -> char ' ' <> pretty ex 

prettyExpr :: Coloring -> Prec -> Exp ctx ty -> Doc
prettyExpr c _    (Var n)          = prettyVar c (elemToInt n)
prettyExpr c prec (Lam body)       = prettyLam c prec Nothing body
prettyExpr c prec (App e1 e2)      = prettyApp c prec e1 e2
prettyExpr c prec (Cond e1 e2 e3)  = prettyIf c prec e1 e2 e3
--prettyExpr c prec (Fix e)          = prettyFix c prec e
prettyExpr _ _    (NatE n)         = int $ natToInt n
prettyExpr _ _    (BoolE True)     = text "true"
prettyExpr _ _    (BoolE False)    = text "false"

prettyExpr c prec rs@(RS rest ex) = char '{' <> prettyRec c prec rs 
  where 
     recLabel :: forall ctx l t xs. SingI (l :: Label) => Exp ctx ('RecTy ('(l,t) ': xs)) -> Doc  
     recLabel (RS _ _) = text . toString . fromSing $ sing @l 
     recLabel _ = error "Non-record expression has record type!"

     prettyRec :: forall ctx t xs. Coloring -> Prec -> Exp ctx (RecTy xs) -> Doc 
     prettyRec c prec recs = case recs of 
      rx@(RS rst ex') ->  recLabel rx 
                       <> char ':' 
                       <+> prettyExpr c prec ex' 
                       <> case rst of 
                            RS {} -> char ',' <+> prettyRec c prec rst 
                            RZ    -> char '}'
                            _ -> error "boom!"
      RZ -> char '}'
      _ -> error "boom!"

prettyExpr c prec Nil = text "[]"

prettyExpr c prec RZ               = text "{}"

prettyExpr c prec (Project n ex (LabelE l)) = prettyExpr c prec ex 
                                           <> char '.' <> text  (toString . fromSing $ l)

prettyExpr c prec (DataCon (LabelE l) _ ex) = (text . toString . fromSing $ l) 
                                         <+> parens (prettyExpr c prec ex) 


prettyExpr c prec (CaseE e1 matches) = text "case"
                                  <+> prettyExpr c prec e1 
                                  <+> text "of"
                                  <+> char '{'
                                  <+> prettyMatches matches
                                  <+> char '}'
  where 
    prettyMatches :: forall ctx arg res. MatchList ctx arg res -> Doc 
    prettyMatches ms = case ms of 
      MS ml di si sPat si2 si3 f -> prettyPat (fromSing sPat) <+> text "=>" <+> prettyExpr c prec f <+> char '|' <+> prettyMatches ml
      MZ d g sPat a r ex -> prettyPat (fromSing sPat) <+> text "=>" <+>  prettyExpr c prec ex






prettyExpr c prec (BinaryOp e1 op e2) = prettyBinOp c prec e1 (demoteOp2 op) e2 
prettyExpr c prec (Cons e1 e2) = text "[" 
                              <+> prettyExpr c prec e1
                              <+> go e2 
  where 
    go :: Exp ctx ty -> Doc 
    go ex = case ex of 
      Nil -> text "]"
      Cons ex1 ex2 -> text "," <+> prettyExpr c prec ex1 <+> go ex2 
      _ -> error "boom!"
 
prettyPat :: Pat -> Doc 
prettyPat p = case p of 
  VarP l -> text (toString l)
  ConP l p' -> text (toString l) <+> prettyPat p' 
  RecP fps  -> char '{' <+> prettyFieldPats fps <+> char '}' 
  NatP n    -> int (natToInt n)
  BoolP b   -> pretty (BoolE b)
  WildP     -> char '_' 
 where 
    prettyFieldPats :: [(Label,Pat)] -> Doc 
    prettyFieldPats [] = text ""
    prettyFieldPats (f:fs) = case f of 
      (l, pat) -> text (toString l) 
                     <> char ':' 
                     <+> prettyPat pat 
                     <> case fs of 
                          [] -> text ""
                          _  -> char ',' <+> prettyFieldPats fs  

---------------- moved here for staging 

-- | @Length xs@ tells you how long a list @xs@ is.
-- @LZ :: Length xs@ says that @xs@ is empty.
-- @LS len :: Length xs@ tells you that @xs@ has one more element
-- than @len@ says.
data Length :: [a] -> * where
  LZ :: Length '[]
  LS :: Length xs -> Length (x ': xs)

type family (xs :: [a]) ++ (ys :: [a]) :: [a]
type instance '[]       ++ ys = ys
type instance (x ': xs) ++ ys = x ': (xs ++ ys)
infixr 5 ++

-- | Convert an expression typed in one context to one typed in a larger
-- context. Operationally, this amounts to de Bruijn index shifting.
-- As a proposition, this is the weakening lemma.
shift :: forall ts2 t ty. Exp ts2 ty -> Exp (t ': ts2) ty
shift = go LZ
  where
    go :: forall ts1 ty. Length ts1 -> Exp (ts1 ++ ts2) ty -> Exp (ts1 ++ t ': ts2) ty
    go l_ts1 (Var v)          = Var (shift_elem l_ts1 v)
    go l_ts1 (Lam body)       = Lam (go (LS l_ts1) body)
    go l_ts1 (App e1 e2)      = App (go l_ts1 e1) (go l_ts1 e2)
    go l_ts1 (BinaryOp e1 op e2) = BinaryOp (go l_ts1 e1) op (go l_ts1 e2)
    go l_ts1 (Cons e1 e2)        = Cons (go l_ts1 e1) (go l_ts1 e2)
    go _ Nil = Nil 
    go l_ts1 (Cond e1 e2 e3)  = Cond (go l_ts1 e1) (go l_ts1 e2) (go l_ts1 e3)
    go l_ts1 (CaseE e1 matches) = CaseE (go l_ts1 e1) (shiftMatches l_ts1 matches)
          where 
        shiftMatches :: forall arg res 
                      . Length ts1 
                    -> MatchList (ts1 ++ ts2) arg res  
                    -> MatchList  (ts1 ++ t ': ts2) arg res 
        shiftMatches l m = unsafeCoerce m  
    go l_ts1  RZ              = RZ 
    go l_ts1  (RS rs ex)      = RS (go l_ts1 rs) (go l_ts1 ex)
    go l_ts1 (Project n rEx l)  = Project n (go l_ts1 rEx) l
    go l_ts1 (DataCon l t ex)     = DataCon l t (go l_ts1 ex)  
    go _     (NatE n)         = NatE n
    go _     (BoolE b)        = BoolE b


    shift_elem :: Length ts1 -> Elem (ts1 ++ ts2) x
               -> Elem (ts1 ++ t ': ts2) x
    shift_elem LZ     e      = ES e
    shift_elem (LS _) EZ     = EZ
    shift_elem (LS l) (ES e) = ES (shift_elem l e)

-- | Substitute the first expression into the second. As a proposition,
-- this is the substitution lemma.
subst :: forall ts2 s t.
         Exp ts2 s -> Exp (s ': ts2) t -> Exp ts2 t
subst e = go LZ
  where
    go :: forall ts1 t. Length ts1 -> Exp (ts1 ++ s ': ts2) t -> Exp (ts1 ++ ts2) t
    go len (Var v)          = subst_var len v
    go len (Lam body)       = Lam (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (BinaryOp e1 op e2) = BinaryOp (go len e1) op (go len e2)
    go len (Cons e1 e2)     = Cons (go len e1) (go len e2)
    go len Nil              = Nil 
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (CaseE e1 matches) = CaseE (go len e1) (subMatches len matches) 
    go len RZ               = RZ 
    go len (RS rEx ex)      = RS (go len rEx) (go len ex)
    go len (Project n rEx l)  = Project n (go len rEx) l
    go len (DataCon l st ex)     = DataCon l st (go len ex) 
   -- go len (Fix e)          = Fix (go len e)
    go _   (NatE n)         = NatE n
    go _   (BoolE b)        = BoolE b

    subst_var :: forall ts1 t.
                 Length ts1 -> Elem (ts1 ++ s ': ts2) t
              -> Exp (ts1 ++ ts2) t
    subst_var LZ     EZ       = e
    subst_var LZ     (ES v)   = Var v
    subst_var (LS _) EZ       = Var EZ
    subst_var (LS len) (ES v) = shift (subst_var len v)

    subMatches :: forall ts1 arg t
                . Length ts1 
                -> MatchList (ts1 ++ s ': ts2) arg t 
               -> MatchList (ts1 ++ ts2) arg t
    subMatches len ml = unsafeCoerce ml   

apply :: Val (arg :-> res) -> Exp '[] arg -> Exp '[] res
apply (LamVal body) arg = subst arg body



---- remove in favor of Unique class from Utils 
class UniqueL (recName :: Label) (l :: Label) (xs :: [(Label,Ty)])

instance ( UniqueL recName l xs 
         , UniqueL recName x xs) => UniqueL recName s ( '(x,_f) ': xs)

type AllValFields :: [(k,Ty)] -> Constraint 
type family AllValFields fs where
  AllValFields '[] = ()
  AllValFields ( '(k,t) ': xs) = (GlamVal t, AllValFields xs) 

data RecValList :: Ty -> Type where 
  RValZ ::  RecValList (RecTy  '[])

  RValS :: RecValList (RecTy xs) 
       -> Sing (l :: Label) 
       -> Exp '[] (t :: Ty) 
       -> RecValList (RecTy  ( '(l,t) ': xs)) 
