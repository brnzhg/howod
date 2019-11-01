
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE DuplicateRecordFields #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}


module Data.Vector.GDP.Sorted2 (
 ) where

import Data.Ord (comparing)
import Data.Function (on)
import Data.Bool (bool)
import Data.Maybe (fromMaybe)

import qualified Data.Foldable as FLD

import Data.Coerce
import Data.Proxy

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.State.Strict
import Control.Monad.Loops (untilJust)
import Control.Arrow ((&&&))

import qualified Data.Finite as F

import qualified Data.Vector.Generic.Base as VGB
import qualified Data.Vector.Generic.Sized as VGS

import qualified Numeric.Interval.NonEmpty as IVL

import GHC.TypeNats

import qualified GDP
import GDP.Theory.VectorBasic (IsVector, vectorIsVector)
import Data.Vector.GDP.Sorted (Comparison)
import qualified Data.Vector.GDP.Sorted as GDPVS
import GDP.Theory.RecordField

--TODO look at how internal modules work, do that

--TODO alternative approach, 
--theory of intervals
--lots more boilerplate
newtype IsCmpVecOf cmpName vecName cmpVecName = IsCmpVecOf GDP.Defn
type role IsCmpVecOf nominal nominal nominal

newtype SortedCmpVec cmpVecName = SortedCmpVec GDP.Defn
type role SortedCmpVec nominal


data CmpVector v (n :: Nat) e = CmpVector {
  cmpVecCmp :: Comparison e
  , cmpVecVec :: VGS.Vector v n e
}

makeCmpVectorOf :: (VGB.Vector v e)
  => (Comparison e GDP.~~ cmpName)
  -> (VGS.Vector v n e GDP.~~ vName)
  -> (CmpVector v n e GDP.?IsCmpVecOf cmpName vName)
makeCmpVectorOf (GDP.The cmp) (GDP.The v) = GDP.assert
  $ CmpVector { cmpVecCmp = cmp, cmpVecVec = v }

instance HasNamedField "Cmp" (CmpVector v n e) (Comparison e) where
  --getNamedField :: (CmpVector v n e GDP.~~ cmpVecName) 
  -- -> (Comparison e GDP.~~ IsFieldOf "Cmp" cmpVecName)
  getNamedField _ = GDP.defn . cmpVecCmp . GDP.the

instance (VGB.Vector v e) => HasNamedField "Vec" (CmpVector v n e) (VGS.Vector v n e) where
  getNamedField _ = GDP.defn . cmpVecVec . GDP.the

instance PropHasField "Cmp" (IsCmpVecOf cmpName vName) cmpName where
  --matchPropField :: GDP.Proof (IsCmpVecOf cmpName vName cvName)
  --  -> GDP.Proof (IsFieldOf "Cmp" cvName GDP.== cmpName)
  matchPropField _ _ = GDP.axiom

instance PropHasField "Vec" (IsCmpVecOf cmpName vName) vName where
  matchPropField _ _ = GDP.axiom



sortedCmpVecFromSortedVec
  :: GDP.Proof (GDPVS.SortedBy (IsFieldOf "Cmp" cvName) (IsFieldOf "Vec" cvName))
  -> GDP.Proof (SortedCmpVec cvName)
sortedCmpVecFromSortedVec _ = GDP.axiom

sortedVecFromSortedCmpVec
  :: GDP.Proof (SortedCmpVec cvName)
  -> GDP.Proof (GDPVS.SortedBy (IsFieldOf "Cmp" cvName) (IsFieldOf "Vec" cvName))
sortedVecFromSortedCmpVec _ = GDP.axiom


testProof :: GDP.Proof (IsCmpVecOf cmpName vName cvName)
  -> GDP.Proof (GDPVS.SortedBy cmpName vName) 
  -> GDP.Proof (SortedCmpVec cvName)
testProof isCmpVecProof =
  sortedCmpVecFromSortedVec
  . GDP.substitute (GDP.arg :: GDP.Arg GDP.LHS) matchCmp
  . GDP.substitute (GDP.arg :: GDP.Arg GDP.RHS) matchVec
  where
    matchCmp = GDP.symmetric $ matchPropField (Proxy :: Proxy "Cmp") isCmpVecProof
    matchVec = GDP.symmetric $ matchPropField (Proxy :: Proxy "Vec") isCmpVecProof







--test
cmpOfIsCmpVec :: GDP.Proof (IsCmpVecOf cmpName vName cvName) 
  -> GDP.Proof (IsFieldOf "Cmp" cvName GDP.== cmpName)
cmpOfIsCmpVec = matchPropField Proxy


--cmpVectorIsCmpVecOf :: 
-- GDP.Proof (IsCmpVecOf (CmpVecCmp cvName) (CmpVecVec cvName) cmpVecName)
-- cmpVectorIsCmpVecOf = GDP.axiom


