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
             
             
module Language.Glee.Match where

import Language.Glee.Pat 
import Language.Glee.Type 
import Language.Glee.Exp 

