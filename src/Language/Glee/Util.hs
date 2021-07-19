{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs, PolyKinds, TypeOperators, CPP, RankNTypes, TypeApplications, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-warnings-deprecations #-}


module Language.Glee.Util (
  render, toSimpleDoc, maybeParens, ($$),
  Prec, topPrec,
  stripWhitespace, nthDefault,
  (:~:)(..), ignore, HList(..), hLookup, hInsert, hInsert', Unique(..), mkUniqueDict
  ) where

import Text.Megaparsec
import Text.PrettyPrint.ANSI.Leijen as Pretty

import Data.Char
import Data.List

#if __GLASGOW_HASKELL__ < 709
import Data.Functor
#endif

#if __GLASGOW_HASKELL__ >= 707
import Data.Type.Equality
import Data.Kind
import Data.Singletons.Decide
import Data.Singletons
import Data.Constraint 
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.List
import qualified Data.Singletons.Prelude.Eq as SEq
#else
data a :~: b where
  Refl :: a :~: a
#endif

-- | Like 'Data.Functor.void'
ignore :: Functor f => f a -> f ()
ignore = (() <$)

--instance Pretty ParseError where
--  pretty = text . show

-- | More perspicuous synonym for operator precedence
type Prec = Rational

-- | Precedence for top-level printing
topPrec :: Prec
topPrec = 0

-- | Convert a 'Doc' to a 'String'
render :: Doc -> String
render = flip displayS "" . toSimpleDoc

-- | Convert a 'Doc' to a 'SimpleDoc' for further rendering
toSimpleDoc :: Doc -> SimpleDoc
toSimpleDoc = renderPretty 1.0 78

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id

-- | Synonym for 'Pretty.<$>'
($$) :: Doc -> Doc -> Doc
($$) = (Pretty.<$>)

-- | (Inefficiently) strips whitespace from a string
stripWhitespace :: String -> String
stripWhitespace = dropWhile isSpace . dropWhileEnd isSpace

-- | Pluck out the nth item from a list, or use a default if the list
-- is too short
nthDefault :: a -> Int -> [a] -> a
nthDefault _   0 (x:_)  = x
nthDefault def n (_:xs) = nthDefault def (n-1) xs
nthDefault def _ []     = def

-- | Type class to enforce uniqueness in type-level list
class Unique (xs :: [k])

instance Unique '[]

instance (Unique xs, TestUnique x xs ~ True) => Unique (x ': xs)

-- | Tests whether a type-level list is unique
type TestUnique :: k -> [k] -> Bool 
type family TestUnique k ks where 
  TestUnique _k '[] = 'True 
  TestUnique k  (k' ': ks) = Not (k SEq.== k') && (TestUnique k ks && TestUnique k' ks) 

sTestUnique :: forall k (a :: k) (as :: [k])
             . SEq.SEq k => Sing a -> Sing as -> Sing (TestUnique a as)
sTestUnique a SNil = STrue 
sTestUnique a (SCons x xs) 
  = sNot (a SEq.%== x) %&& (sTestUnique a xs  %&& sTestUnique x xs )

mkUniqueDict :: forall k (as :: [k]) (a :: k)
              . (SEq.SEq k, Unique as) 
             => Sing a 
             -> Sing as 
             -> Maybe (Dict (Unique (a ': as))) 
mkUniqueDict a as = case as of 
  SNil -> Just Dict
  xss@(SCons x xs) -> case sTestUnique a xss  of 
    STrue -> Just Dict 
    SFalse -> Nothing 
  
data HList :: (k -> Type) -> [k] -> Type where 
  HZ :: forall k (c :: k -> Type). HList c '[]
  HS :: forall k (c :: k -> Type) (a :: k) (as :: [k])
      . (SDecide k, SingI a, Unique (a ': as)) 
     => HList c as -> c a -> HList c (a ': as)  

getSing :: forall x xs c. HList c (x ': xs) -> Sing x 
getSing HS {} = sing  

getSings :: forall x xs c. HList c xs -> Sing xs 
getSings hl = case hl of  
  HZ -> sing @'[]
  hs@(HS hl' cx) -> getSing hs `SCons` getSings hl' 

hLookup :: forall k (a ::k) (as :: [k]) (c :: k -> Type)
         . Sing a -> HList c as -> Maybe (c a)
hLookup a hl = case hl of 
  HZ -> Nothing 
  hs@(HS hl' cx) -> case decideEquality (getSing hs) a of 
    Just Refl -> Just cx
    Nothing   -> hLookup a hl'    

hInsert :: forall k (a :: k) (as :: [k]) (c :: k -> Type)
         . (SDecide k, SingI a, SEq.SEq k) =>  c a -> HList c as -> Either String (HList c (a ': as) )
hInsert ca hl = case hl of 
  HZ -> withSingI (sing @a) $ Right $ HS HZ ca 
  hs@(HS hl' _) -> case mkUniqueDict (sing @a) (getSings hs) of 
    Just Dict -> Right $ HS hs ca
    Nothing   -> Left "Cannot insert into HList: Item is a duplicate!"

hInsert' :: forall k (a :: k) (as :: [k]) (c :: k -> Type)
         . (SDecide k, SingI a, SEq.SEq k, Unique (a ': as)) 
        =>  c a -> HList c as ->  (HList c (a ': as) )
hInsert' ca hl = case hl of 
  HZ -> withSingI (sing @a) $  HS HZ ca 
  hs@(HS hl' _) -> HS hs ca
