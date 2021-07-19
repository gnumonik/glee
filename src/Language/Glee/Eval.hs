{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             DataKinds, TypeFamilies, PolyKinds,
             GADTs, BangPatterns, AllowAmbiguousTypes, TypeApplications, LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}


module Language.Glee.Eval ( eval ) where

import Language.Glee.Exp hiding (apply)
import Language.Glee.Token
import Language.Glee.Nat 
import Control.Monad.Identity
import Language.Glee.Type 
import Data.Singletons
import Language.Glee.Ascii
import Language.Glee.Hasochism
import Language.Glee.Pat 
import Data.Constraint
import Unsafe.Coerce 
import Data.Coerce
import Data.Function ((&))
import Data.Singletons.Decide
import Data.Singletons.Prelude.List (SList(..))
import Data.Singletons.Prelude.Tuple
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Bool
import Data.Maybe (fromJust)
import Data.Singletons.Prelude.Maybe

-- | Given a lambda and an expression, beta-reduce.
apply :: Val (arg :-> res) -> Exp '[] arg -> Exp '[] res
apply (LamVal body) arg = subst arg body

-- | Conditionally choose between two expressions
cond :: Val BoolTy -> Exp '[] t -> Exp '[] t -> Exp '[] t
cond (BoolVal True)  e _ = e
cond (BoolVal False) _ e = e

subPat :: MatchPatTy p arg => Exp '[] arg -> Exp '[] (arg :-> res) -> Exp '[] res  
subPat arg matchBody = runIdentity $ do 
  vBody <- pure $ eval matchBody 
  pure $ apply vBody arg

mkMatchVals :: forall p arg
             . Sing (p :: Pat) -> Sing arg -> Exp '[] arg -> Maybe (ValList (Guard p arg))
mkMatchVals  sPat sArg ex = case sPat of 
  SVarP _ -> Just $ VS VZ sArg ex 
  SWildP  -> Just VZ 
  SConP l p' -> case sArg of 
    SVariantTy fs -> goVariant (SConP l p') (SVariantTy fs)  ex 
    _ -> Nothing 
  SRecP fps -> case sArg of 
    SRecTy fs ->  goRec (SRecP fps) (SRecTy fs) ex 
    _ -> Nothing 
  SNatP sn -> case sArg of 
    SNatTy -> case eval ex of 
      NatVal n -> if n == fromSing sn then Just VZ else Nothing 
    _ -> Nothing  
  SBoolP sb -> case sArg of 
    SBoolTy -> case eval ex of 
      BoolVal b -> if b == fromSing sb then Just VZ else Nothing 
    _ -> Nothing  
 where


   goVariant :: forall (l :: Label) (p :: Pat) (fs :: [(Label,Ty)])
              . Sing ('ConP l p) 
             -> Sing ('VariantTy fs)
             -> Exp '[] ('VariantTy fs)
             -> Maybe (ValList (Guard ('ConP l p)  ('VariantTy fs)))
   goVariant _ (SVariantTy SNil) _ = Nothing 
   goVariant  sp@(SConP l p') (SVariantTy vs@(SCons (STuple2 l' t) xs)) ex 
      = goHelper sp vs ex 
    where 
      goHelper :: forall vs l' ty ts 
               . Sing ('ConP l p) 
              -> Sing (vs :: [(Label,Ty)])
              -> Exp '[] (VariantTy fs)
              -> Maybe (ValList (GoConP ('ConP l p) vs))
      goHelper (SConP lx px) SNil _ = Nothing 
      goHelper pp@(SConP lx px) (SCons (STuple2 lv tv) xs) ex =  
        case lx %== lv of 
          STrue -> case val . eval $ ex of 
            DataCon (LabelE le) st ee -> 
              case decideEquality st tv of 
                  Just Refl -> mkMatchVals px tv ee
                  Nothing -> Nothing 
            _ -> Nothing 
          SFalse -> goHelper pp xs ex 
 
   goRec :: forall (fps :: [(Label,Pat)]) (fs :: [(Label,Ty)])
          . Sing ('RecP fps) 
         -> Sing ('RecTy fs)
         -> Exp '[] ('RecTy fs)
         -> Maybe (ValList (FieldGuards fps fs))
   goRec (SRecP fps) (SRecTy fs) e = case (fps, fs) of 
     (SNil,SNil) -> Just VZ
     (SCons (STuple2 l p) ps, SCons (STuple2 l' ft) fs') -> case l %== l' of 
       SFalse -> Nothing 
       STrue -> case e of 
         RS rest ex -> case mkMatchVals p ft ex of 
           Nothing -> Nothing 
           Just vl -> case goRec (SRecP ps) (SRecTy fs') rest of 
             Nothing -> Nothing 
             Just vls -> Just $ vAppend vl vls   
         _ -> Nothing 
     _ -> Nothing 
     
evalCase' :: forall res. Exp '[] res -> Val res
evalCase' (CaseE ex matches) = fromJust $ go ex matches 
  where 
    go :: forall arg. Exp '[] arg -> MatchList '[] arg res -> Maybe (Val res) 
    go e m = case m of 
      mz@(MZ d w p a r f) -> case mkMatchVals p a e of 
        Just vlist -> Just . eval $  (processMatch w f) vlist  
        Nothing -> error "Non-exhaustive patterns in case expression!"
      ms@(MS rest d w p a r  f) -> case mkMatchVals p a e of 
        Just vlist -> Just . eval $ (processMatch w f) vlist
        Nothing -> go e rest  

evalCase' _ = error "BOOM!"



-- | Unroll a `fix` one level
--unfix :: Val (ty -> ty) -> Exp '[] ty
--unfix (LamVal body) = subst (Fix (Lam body)) body

-- | A well-typed variable in an empty context is impossible.
impossibleVar :: Elem '[] x -> a
impossibleVar _ = error "GHC's typechecker failed"
  -- GHC 7.8+ supports EmptyCase for this, but the warnings for that
  -- construct don't work yet.

-- | Evaluate an expression, using big-step semantics.
eval :: forall (t :: Ty). Exp '[] t -> Val t
eval exp = case nf exp of 
  (Var v)          -> impossibleVar v

  (Lam body)       -> LamVal body

  (App e1 e2)      -> runIdentity $ do 
    !v1 <- pure $ eval e1 
    pure $! eval (apply v1 e2) -- eval (apply (eval e1) e2)

  --(CaseE ex1 (Match p ex2)) -> su


  (BinaryOp e1 op e2) -> runIdentity $ do 
    v1 <- pure $ eval e1 
    v2 <- pure $ eval e2 
    pure $ evalBinOp v1 op v2 

  (Cond e1 e2 e3)  -> eval (cond (eval e1) e2 e3)

--eval (Fix e)          = eval (unfix (eval e))

  (NatE n)         -> NatVal n

  (BoolE b)        -> BoolVal b

  Nil              -> ListVal []

  (Cons e1 e2)     -> ListVal $ (nf e1) : go (nf e2) 
    where 
      go :: Exp '[] (ListTy ty) -> [Exp '[] ty]
      go x = case x of 
        Nil -> []
        Cons ex ey -> (nf $ ex) : go ey 
        other -> go (nf $ other)

  RZ -> RecVal RValZ 

  RS rest ex -> case eval rest of 
    RecVal x ->  RecVal (RValS x sing ex )

  pr@(Project _ rEx l) -> lookupField' pr 

  DataCon (LabelE l) st ex ->  VVal (VValBox l st ex)

  CaseE ex matches -> evalCase' (CaseE ex matches)

-- partial - need to split it out for scoping/inference reasons. could fix by figuring out how to pass a typeclass dict manually or restructuring the eval function 
lookupField' :: Exp '[] t -> Val t 
lookupField' pr = case pr of 
  Project n rEx lbl -> lookupField  n rEx lbl 
  _ -> error "lookupField' called on a non-record expression"
 
lookupField :: forall n l res fs ctx
             . ( HasFieldC' n l res fs 
               , LabelType l fs ~ Just res)
            => Sing n 
            -> Exp '[] (RecTy fs)
            -> LabelE l 
            -> Val res 
lookupField n e (LabelE l) 
    = getField (hasField' n (Proxy @l) (Proxy @res) (Proxy @fs)) (eval e)
  where 
    getField :: forall v (l :: Label) (res :: Ty) (fs :: [(Label,Ty)])
              . HasField l res fs -> Val ('RecTy fs) -> Val res 
    getField hf (RecVal (RValS rList l v)) = case hf of 
      FHere -> eval v 
      FThere hfs -> getField hfs (RecVal rList)

nf :: Exp '[] t -> Exp '[] t 
nf e = case e of 
  Var v -> Var v 

  Lam body -> Lam  body 

  App e1 e2 -> case (nf e1) of 
    Lam body -> nf $ subst (nf e2) body 
    ne1 -> App ne1 (nf e2)

  BinaryOp e1 op e2 -> val $ evalBinOp (eval e1) op (eval e2)

  Cons e1 e2 -> Cons (nf e1) (nf e2)

  Nil        -> Nil 

  Cond e1 e2 e3 -> Cond (nf e1) (nf e2) (nf e3)

  NatE n -> NatE n 

  BoolE b -> BoolE b 

  RZ         -> RZ 

  RS rEx ex  -> RS (nf rEx) (nf ex)

  Project n rEx l -> Project n (nf rEx) l

  DataCon l st ex    -> DataCon l st (nf ex)

  _ -> e 

{--

-- | Step an expression, either to another expression or to a value.
step :: Exp '[] t -> Either (Exp '[] t) (Val t)
step (Var v)          = impossibleVar v

step (Lam body)       = Right (LamVal body)

step (App e1 e2)      = case step e1 of
                          Left e1' -> Left (App e1' e2)
                          Right (LamVal body) -> Left (subst e2 body)

step (BinaryOp e1 op e2) = case step e1 of 
  Left e1' -> Left (BinaryOp e1' op e2)
  Right v1 -> case step e2 of 
    Left e2' -> Left (BinaryOp e1 op e2')
    Right v2 -> Left (BinaryOp e1 op e2)
{--
step (Arith e1 op e2) = case step e1 of
                          Left e1' -> Left (Arith e1' op e2)
                          Right v1 -> case step e2 of
                            Left e2' -> Left (Arith (val v1) op e2')
                            Right v2 -> Left (arith v1 op v2)
--}
step (Cond e1 e2 e3)  = case step e1 of
                          Left e1' -> Left (Cond e1' e2 e3)
                          Right v1 -> Left (cond v1 e2 e3)

--step (Fix e)          = case step e of
--                          Left e' -> Left (Fix e')
--                          Right v -> Left (unfix v)

step (NatE n)         = Right (NatVal n)

step (BoolE b)        = Right (BoolVal b)

--}
