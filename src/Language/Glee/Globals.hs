{-# LANGUAGE GADTs, DataKinds, RankNTypes, FlexibleContexts, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}

module Language.Glee.Globals  where

import Language.Glee.Exp
import Language.Glee.Type

import Text.PrettyPrint.ANSI.Leijen
import Control.Lens.TH (makeLenses)
import Control.Monad.Error

import Data.Map as Map
import Data.Text
import Language.Glee.Ascii
import Language.Glee.Hasochism

-- | An existential wrapper around 'Exp', storing the expression and
-- its type.
data EExp where
  EExp :: STy ty -> Exp '[] ty -> EExp

-- | The global variable environment maps variables to type-checked
-- expressions
data  Globals = Globals {_globalVars :: Map Label EExp
                        ,_globalContext :: Context}
makeLenses ''Globals 

-- | An empty global variable environment
emptyGlobals :: Globals
emptyGlobals = Globals Map.empty initContext 

-- | Extend a 'Globals' with a new binding
extend :: Label -> STy ty -> Exp '[] ty -> Globals -> Globals
extend var sty exp (Globals globals tyCtx)
  = Globals (Map.insert var (EExp sty exp) globals) tyCtx 

-- | Lookup a global variable. Fails with 'throwError' if the variable
-- is not bound.
lookupGlobal :: MonadError Doc m
             => Globals -> Label
             -> (forall ty. STy ty -> Exp '[] ty -> m r)
             -> m r
lookupGlobal (Globals globals tyCtx) var k
  = case Map.lookup var globals of
      Just (EExp sty exp) -> k sty exp
      Nothing             -> throwError $
                             text "Global variable not in scope:" <+>
                               squotes (text $ toString var)
