
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
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

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.State.Strict
import Control.Monad.Loops (untilJust)
import Control.Arrow ((&&&))

import qualified Data.Finite as F

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Base as VGB
import qualified Data.Vector.Generic.Mutable.Base as VGMB

import qualified Data.Vector.Sized as VS
import qualified Data.Vector.Generic.Sized as VGS
import qualified Data.Vector.Generic.Mutable.Sized as VGMS
import Data.Vector.Generic.Mutable.Sized.Internal (MVector(..))

import qualified Data.Vector.Algorithms.Intro as VAI
import Data.Vector.Algorithms.Intro (Comparison)

import qualified Numeric.Interval.NonEmpty as IVL

import GHC.TypeNats

import qualified GDP

--TODO alternative approach, 
--theory with IndexOfSorted i x
--theory of intervals
--lots more boilerplate
newtype IsCmpVecOf cmpName vecName cmpVecName = IsCmpVecOf GDP.Defn
type role IsCmpVecOf nominal nominal nominal

newtype CmpVecVec cmpVecName = CmpVecVec GDP.Defn
type role CmpVecVec nominal

newtype CmpVecCmp cmpVecName = CmpVecCmp GDP.Defn
type role CmpVecCmp nominal


newtype SortedBy comp name = SortedBy GDP.Defn
type role SortedBy nominal nominal

newtype SortedByOf e cmp name = SortedByOf GDP.Defn
type role SortedByOf representational nominal nominal

newtype CmpVecSorted cmpVecName = CmpVecSorted GDP.Defn
type role CmpVecSorted nominal

type FinInterval (n :: Nat) = IVL.Interval (F.Finite n)

--interval includes index of first element >= search element

newtype SortedInsertSearchOf cmpVecName elemName searchName = SortedInsertSearchOf GDP.Defn
type role SortedInsertSearchOf nominal nominal nominal

newtype SortedInsertIdx cmpVecName elemName idxName = SortedInsertIdx GDP.Defn
type role SortedInsertIdx nominal nominal nominal


data CmpVector v n e = CmpVector {
  cmpVecCmp :: Comparison e
  , cmpVecVec :: VGS.Vector v n e
}


--TODO when do you want Is proofs, when do you just want names?
makeCmpVectorOf :: (VGB.Vector v e)
  => (Comparison e GDP.~~ cmpName)
  -> (VGS.Vector v n e GDP.~~ vName)
  -> (CmpVector v n e GDP.?IsCmpVecOf cmpName vName)
makeCmpVectorOf (GDP.The cmp) (GDP.The v) = GDP.assert
  $ CmpVector { cmpVecCmp = cmp, cmpVecVec = v }

getCmpOfCmpVector :: (CmpVector v n e GDP.~~ cmpVecName) 
  -> (Comparison e GDP.~~ CmpVecCmp cmpVecName)
getCmpOfCmpVector = GDP.defn . cmpVecCmp . GDP.the

getVecOfCmpVector :: (VGB.Vector v e)
  => (CmpVector v n e GDP.~~ cmpVecName)
  -> (VGS.Vector v n e GDP.~~ CmpVecVec cmpVecName)
getVecOfCmpVector = GDP.defn . cmpVecVec . GDP.the


--TODO what the hell to name this
cmpOfIsCmpVecOf :: GDP.Proof (IsCmpVecOf cmpName vName cmpVecName)
  -> GDP.Proof (CmpVecCmp cmpVecName GDP.== cmpName)
cmpOfIsCmpVecOf _ = GDP.axiom

vecOfIsCmpVecOf :: GDP.Proof (IsCmpVecOf cmpName vName cmpVecName)
  -> GDP.Proof (CmpVecVec cmpVecName GDP.== vName)
vecOfIsCmpVecOf _ = GDP.axiom

--TODO is constraint necessary? is this gonna break things?
cmpVectorIsCmpVecOf :: 
  GDP.Proof (IsCmpVecOf (CmpVecCmp cmpVecName) (CmpVecVec cmpVecName) cmpVecName)
cmpVectorIsCmpVecOf = GDP.axiom
-- (VGP.Vector v e) 
-- => (CmpVector v n e GDP.~~ cmpVecName)


sortByAndFreeze :: (PrimMonad m, VGB.Vector v e) 
  => (Comparison e GDP.~~ cmp)
  -> VGMS.MVector (VG.Mutable v) n (PrimState m) e 
  -> m (VGS.Vector v n e GDP.?SortedBy cmp)
sortByAndFreeze (GDP.The cmp) vm@(MVector v) = do
  VAI.sortBy cmp v
  GDP.assert <$> VGS.freeze vm

{- 
sortedInsertWholeIndexInterval :: (KnownNat n, GDP.Fact (SortedByOf e cmp vName))
  => (e GDP.~~ eName)
  -> FinInterval (n + 1) GDP.?SortedInsertSearchOf cmp vName eName
sortedInsertWholeIndexInterval e = GDP.assert 
  $ (minBound IVL.... maxBound) 
-}

