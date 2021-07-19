{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE PolyKinds #-} 
{-# LANGUAGE GADTs #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE CPP #-} 
{-# LANGUAGE LambdaCase #-} 
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}
{-# OPTIONS -Wall #-} 
#ifdef __HADDOCK_VERSION__
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#endif

module Language.Glee.Check ( check ) where

import Language.Glee.Exp 
import Language.Glee.Type
import Language.Glee.Unchecked
import Language.Glee.Util
import Language.Glee.Globals
#ifdef __HADDOCK_VERSION__
import Language.Glee.Monad ( GlamE )
#endif
import qualified Data.Singletons.Prelude.List as SList 
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Control.Lens (view)
import Control.Monad.Reader
import Control.Monad.Except 
import Data.Singletons
import Data.Kind (Type)
import Data.Singletons.Prelude.Tuple
import Language.Glee.Ascii (Label, toString)

import qualified Data.Singletons.Prelude as S
import Data.Constraint
import Data.Singletons.Decide
import Language.Glee.Hasochism
import Data.Singletons.Prelude.List hiding (Elem(..))
import Language.Glee.Op2 
import Language.Glee.Pat


-- | Abort with a type error in the given expression
typeError :: MonadError Doc m => UExp -> Doc -> m a
typeError e doc = throwError $
                  doc $$ text "in the expression" <+> squotes (pretty e)

lookupDataCon :: MonadReader Globals m 
              => Sing (l :: Label) -> m (Maybe (ConstructorInfo l))
lookupDataCon l = asks (view (globalContext . dataCons)) >>= \case 
  Some hList -> pure $ hLookup l hList 

------------------------------------------------
-- The typechecker

-- | Check the given expression, aborting on type errors. The resulting
-- type and checked expression is given to the provided continuation.
-- This is parameterized over the choice of monad in order to support
-- pure operation during testing. 'GlamE' is the canonical choice for the
-- monad.
check :: (MonadError Doc m, MonadReader Globals m)
      => UExp 
      -> (forall t. STy t -> Exp '[] t -> m r)
      -> m r
check = go emptyContext
  where
    go :: forall m ctx r. (MonadError Doc m, MonadReader Globals m)
       => SCtx ctx -> UExp -> (forall t. STy t -> Exp ctx t -> m r)
       -> m r

    go ctx (UVar n) k
      = checkVar ctx n $ \ty elem' ->
        k ty (Var elem')

    go ctx (UGlobal n) k
      = do globals <- ask
           lookupGlobal globals n $ \ty exp' ->
             k ty (shiftIntoCtx ctx exp')

    go ctx (ULam ty body) k
      = refineTy ty $ \arg_ty ->
        go (arg_ty `SCons` ctx) body $ \res_ty body' ->
        k (arg_ty :%-> res_ty) (Lam body')

    go ctx e@(UApp e1 e2) k
      = go ctx e1 $ \ty1 e1' ->
        go ctx e2 $ \ty2 e2' ->
        case (ty1, ty2) of
          (arg_ty :%-> res_ty, arg_ty')
            |  Just Refl <- arg_ty `eqSTy` arg_ty'
            -> k res_ty (App e1' e2')
          _ -> typeError e $
               text "Bad function application." $$
               indent 2 (vcat [ text "Function type:" <+> pretty ty1
                              , text "Argument type:" <+> pretty ty2 ])

    go ctx (UBinOp e1  op e2) k
      = go ctx e1 $ \sty1 e1' ->
        go ctx e2 $ \sty2 e2' ->
        case promoteOp2 op of 
          Some bOP ->  checkBinOp bOP sty1 e1' sty2 e2' $ uncurry k  

    go ctx e@(UCons e1 e2) k 
      = case e2 of 
          UNil _ -> go ctx e1 $ \sty1 e1' -> k (SListTy sty1) (Cons e1' Nil) 
          _ -> go ctx e1 $ \sty1 e1' -> 
               go ctx e2 $ \sty2 e2' -> 
               case sty2 of 
                  SListTy t 
                    | Just Refl <- sty1 `eqSTy` t 
                    -> k sty2 (Cons e1' e2')
                  _ -> typeError e $ 
                        text "Bad cons application: Type mismatch" $$ 
                        indent 2 (vcat [text " First Cons arg type: " <+> pretty sty1
                                      ,text " Second Cons arg type: " <+> pretty sty2])

    go _ e@(UNil mty ) k
      = case mty of 
          Just ty ->  refineTy ty $ \sty1 -> case sty1 of  
              SListTy _ -> k sty1 Nil
              _ -> typeError e $ 
                   text "Bad Nil. Expected a List type but got: " <+> pretty sty1 

          Nothing -> typeError e $ 
                  text "Bad Nil - Cannot infer type of the List."   


    go ctx e@(UCond e1 e2 e3) k
      = go ctx e1 $ \sty1 e1' ->
        go ctx e2 $ \sty2 e2' ->
        go ctx e3 $ \sty3 e3' ->
        case sty1 of
          SBoolTy
            |  Just Refl <- sty2 `eqSTy` sty3
            -> k sty2 (Cond e1' e2' e3')
          _ -> typeError e $
               text "Bad conditional." $$
               indent 2 (vcat [ text "Flag type:" <+> pretty sty1
                              , squotes (text "true") <+> text "expression type:"
                                                      <+> pretty sty2
                              , squotes (text "false") <+> text "expression type:"
                                                       <+> pretty sty3 ])

    go ctx e@(URec es) k = checkFields es >>= \case   
      (Some (RecBox sty ex)) ->   k sty ex 
      where 
        checkFields :: [(UExp,UExp)] -> m (Some (RecBox ctx))
        checkFields xs =  case xs of 
            [] -> pure . Some $ RecBox (SRecTy SList.SNil) RZ
            (y:ys) -> case y of 
              (UGlobal l, exY) -> go ctx exY $ \styY exY' -> -- using UGlobal is bad here 
                  checkFields ys >>= \case                -- need to sort out names 
                    Some (RecBox (SRecTy stYS) exYS) ->
                      case toSing l of 
                        SomeSing l' -> 
                          pure $ Some (RecBox 
                                  (SRecTy $ STuple2 l' styY `SList.SCons` stYS) 
                                  (withSingI l' $ RS exYS exY'))
              (other,_) -> typeError e $ 
                        text "Bad Record!" $$ 
                        indent 2 ( text "The expression" 
                                  <+> pretty other 
                                  <+> text "is not a label!") 

    go ctx e@(UProject e1 e2) k 
      = case e2 of 
          UGlobal l -> 
            case toSing l of 
              SomeSing l' -> 
                go ctx e1 $ \styR eR' ->
                  case styR of 
                    SRecTy recTypes ->  
                      case lookupFType recTypes l' of 
                        Nothing -> typeError e 
                                $ text "Bad record accessor!" $$ 
                                indent 2 (text "The label"
                                        <+> text (toString l)
                                        <+> text "does not exist in the record." )

                        Just (SomeSing t) -> 
                          case decideHasField recTypes l' t of 
                            Nothing ->  typeError e (text "couldn't typecheck record")
                            Just hx -> case mkFieldBox hx of 
                              Some box -> case mkProject box l' recTypes t eR' of 
                                Just x -> k t x 
                                Nothing -> typeError e (text "couldn't typecheck record")

                    _ -> typeError e $ text "Selector applied to non-record type"
          _ -> typeError e $ text "Not a record selector "

    go ctx e@(UDataCon l e1) k 
      = case toSing l of 
          SomeSing l' -> lookupDataCon l' >>= \case 
            Nothing -> typeError e 
                    $ text "Bad variant constructor!" $$ 
                    indent 2 (text "The constructor " 
                              <+> text (toString l)
                              <+> text "is not in scope." )

            Just (MkConstructor _ eTy vTy) -> 
              go ctx e1 $ \styE e1' -> 
                case decideEquality styE eTy of
                  Nothing -> typeError e 
                           $ text "Bad variant argument type!" $$ 
                           indent 2 (text "The constructor"
                                    <+> text (toString l) 
                                    <+> text "takes an argument of type"
                                    <+> pretty eTy 
                                    <+> text "but its argument expression"
                                    <+> pretty e1' 
                                    <+> text "has type"
                                    <+> pretty styE)
                  -- dunno why ghc can infer the constraints from MkConstructor here but 
                  -- can't for the Project case? 
                  Just Refl -> case vTy of 
                    SVariantTy vs -> case mkAllValDict vs of 
                      Just Dict -> k vTy (DataCon (LabelE l') styE e1')
                      Nothing -> typeError e 
                               $ text ("Impossible error: Variant contains fields which"
                                      <> "cannot reduce to values!")

    go ctx e@(UCase ex1 matches) k = go ctx ex1 $ \sty e1' -> 
        case matches of 
          [] -> typeError e 
              $ text "Empty case expression!"
          ((p,mex):xs) -> case toSing p of 
            SomeSing sPat -> case mkGuards sPat sty of 
              Nothing -> typeError e $ text "Invalid pattern guard"
              Just gs -> go gs mex $ \mRes mex' -> case mkGlamDict sty of
                Nothing   -> typeError e $ text "Not a value (shouldn't happen)"
                Just Dict -> case testMatch sPat sty of 
                    Just Dict -> 
                      checkMatches (MZ 
                                    Dict 
                                    gs
                                    sPat 
                                    sty 
                                    mRes 
                                    mex') sty mRes xs >>= \mm -> 
                                  k mRes (CaseE e1' mm)
                    Nothing -> typeError e $ text "Pattern match failure"
      where 
        -- Problem has something to do with the base types not showing up when we call go (Guard Context) ex 
        checkMatches :: GlamVal arg 
                      => MatchList ctx arg res 
                      -> STy arg 
                      -> STy res 
                      -> [(Pat, UExp)] 
                      -> m (MatchList ctx arg res)
        checkMatches ml _ _ [] = pure ml 
        checkMatches ml sArg sRes ((p,u): xs) = case toSing p of 
          SomeSing sPat -> case testMatch sPat sArg of 
                  Just Dict -> mkMatchE sArg sRes sPat u >>= \(mE,sg) -> 
                           let ml' = mlcons Dict sg sPat sArg sRes mE ml
                           in  checkMatches ml' sArg sRes xs 
                  Nothing -> typeError e $ text "Pattern match failure"
                                
        mkMatchE :: (MonadError Doc m, MonadReader Globals m) 
                => Sing (arg :: Ty) 
                -> Sing (res :: Ty) 
                -> Sing (p :: Pat)
                -> UExp 
                -> m (Exp (Guard p arg) res, Sing (Guard p arg))
        mkMatchE sArg sRes sPat uexp = case mkGuards sPat sArg of 
          Nothing -> typeError e 
                  $ text "Error: Could not match case pattern guard with argument type"

          Just sGuards -> go sGuards uexp $ \eTy ex ->
            case decideEquality eTy sRes of 
                Nothing -> typeError e 
                        $ text "Match expression return type doesn't match!" 
                        $$ indent 2 (vcat [text "Match expr type:" 
                                            <+> pretty ex 
                                            <+> pretty eTy 
                                          ,text "Return type:" <+> pretty sRes
                                          ,text "Type Ctx:" <+> (pretty . fromSing $ ctx)
                                          ,text "Guard ctx:" <+> (pretty.fromSing$sGuards)])
                Just Refl -> pure (ex,sGuards) 

    go _   (UNatE n)  k = k sing (NatE n)
    go _   (UBoolE b) k = k sing (BoolE b)

mkProject :: forall l t fs ctx n.  HasFieldBox l t fs n -> Sing l -> Sing fs -> Sing t -> Exp ctx ('RecTy fs) -> Maybe (Exp ctx t) 
mkProject box sl sfs st ex =  case box of 
  HasFieldBox sn Dict _ ->  case sLabelType sl sfs of 
    S.SJust blah -> case blah %~ st of 
      Proved Refl -> Just $ withSingI sn (Project sn ex (LabelE sl))
      Disproved _ -> Nothing
    S.SNothing -> Nothing  

-- a witness that the index kinds of the type and exp match
data RecBox :: [Ty] -> [(Label,Ty)] -> Type where 
  RecBox :: Sing ('RecTy xs) -> Exp ctx ('RecTy xs) -> RecBox ctx xs   



checkVar :: MonadError Doc m
          => SCtx ctx -> Int
          -> (forall t. STy t -> Elem ctx t -> m r)
          -> m r
checkVar SNil           _ _ = throwError (text "unbound variable")
                             -- shouldn't happen. caught by parser.

-- | Type-check a de Bruijn index variable
checkVar (SCons ty _)   0 k = k ty EZ
checkVar (SCons _  ctx) n k = checkVar ctx (n-1) $ \ty elem' ->
                               k ty (ES elem')

-- | Take a closed expression and shift its indices to make sense in
-- a non-empty context.
shiftIntoCtx :: SCtx ctx -> Exp '[] ty -> Exp ctx ty
shiftIntoCtx SNil             exp' = exp'
shiftIntoCtx (_ `SCons` ctx') exp' = shift $ shiftIntoCtx ctx' exp'
