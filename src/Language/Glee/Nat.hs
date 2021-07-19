{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE StandaloneKindSignatures, OverloadedStrings, UndecidableInstances, DuplicateRecordFields, NoImplicitPrelude #-}

module Language.Glee.Nat where


import Protolude hiding (Nat)
import Data.Aeson ( FromJSON, ToJSON ) 
import Data.Singletons.TH


data Nat 
  = Z 
  | S !Nat deriving (Show, Eq, Generic, FromJSON, ToJSON, Ord)


genSingletons [''Nat]

---- could just convert to/from int but eh lets have fun 
instance Num Nat where 
  Z + x = x 
  x + Z = x 
  S x + S y = x + (S (S y))

  x - Z = x 
  Z - x = Z 
  S x - S y = x - y 

  abs x = x 

  Z * x = Z 
  x * Z = Z 
  x * (S y) = x + (x * y)

  signum _ = S Z 

  fromInteger i = if i <= 0 then Z else S (fromInteger (i - 1))


instance Real Nat where 
  toRational n = toRational (natToInt n)

instance Enum Nat where 
  toEnum i = intToNat i 
  fromEnum n = natToInt n 

instance Integral Nat where 
  quotRem n1 n2 = bimap intToNat intToNat $ quotRem (natToInt n1) (natToInt n2) 
  toInteger n = toInteger (natToInt n)

class (:>=) (n1 :: Nat) (n2 :: Nat)
instance (:>=) 'Z 'Z  
instance (:>=) ('S x) 'Z 
instance n1 :>= n2 => ('S n1) :>= ('S n2)


class (:==) (n1 :: Nat) (n2 :: Nat) 
instance 'Z :== 'Z 
instance n1 :== n2 => ('S n1) :== ('S n2)

class (:<=) (n1 :: Nat) (n2 :: Nat)
instance (:<=) 'Z 'Z 
instance (:<=) 'Z ('S x)
instance (n1 :<= n2) => 'S n1 :<= 'S n2 


intToNat :: Int -> Nat 
intToNat n = if n <= 0 
             then Z
             else S (intToNat (n - 1)) 

natToInt :: Nat -> Int 
natToInt Z = 0 
natToInt (S x) = 1 + natToInt x 


type One = S Z 

type Two = S One 

type Three = S Two 

type Four = S Three 

type Five = S Four 

type Six = S Five 

type Seven = S Six 

type Eight = S Seven 

type Nine = S Eight 

type Ten = S Nine 

type Eleven = S Ten 

type Twelve = S Eleven 

type Thirteen = S Twelve 

type Fourteen = S Thirteen 

type Fifteen = S Fourteen 

type Sixteen = S Fifteen 

type Seventeen = S Sixteen 

type Eighteen = S Seventeen 

type Nineteen = S Eighteen 

type Twenty   = S Nineteen 