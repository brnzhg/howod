{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE RoleAnnotations     #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Vector.GDP.Sorted (
  ) where

import Data.Ord (comparing)
import Data.Function (on)
import Data.Bool (bool)
import Data.Maybe (fromMaybe)
--import Data.Monoid (Sum)
import qualified Data.Foldable as FLD
--import qualified Data.Proxy as PXY
import Data.Coerce

import Control.Monad
import Control.Monad.Primitive

import Control.Arrow ((&&&))
--import Control.Monad.State.Strict

import qualified Data.Finite as F
--import Data.Singletons (Sing, sing, fromSing)
--import Data.Singletons.TypeLits

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Base as VGB
import qualified Data.Vector.Generic.Mutable.Base as VGMB

import qualified Data.Vector.Sized as VS
import qualified Data.Vector.Generic.Sized as VGS
import qualified Data.Vector.Generic.Mutable.Sized as VGMS
import Data.Vector.Generic.Mutable.Sized.Internal (MVector(..))

import qualified Data.Vector.Algorithms.Intro as VAI

import qualified Numeric.Interval.NonEmpty as IVL

import GHC.TypeNats

import qualified GDP


newtype SortedBy comp name = SortedBy GDP.Defn
type role SortedBy nominal nominal


type FinInterval (n :: Nat) = IVL.Interval (F.Finite n)

newtype SortedInsertSearchOf cmp vecName elemName searchName = SortedInsertSearchOf GDP.Defn

type role SortedInsertSearchOf nominal nominal nominal nominal

newtype SortedInsertIdx cmp vecName elemName idxName = SortedInsertIdx GDP.Defn

type role SortedInsertIdx nominal nominal nominal nominal

--newtype MVecSorted comp v (n :: Nat) s a = MVecSorted (VGMS.MVector v n s a)

sortByAndFreeze :: (PrimMonad m, VGB.Vector v e) 
  => (VAI.Comparison e GDP.~~ cmp)
  -> VGMS.MVector (VG.Mutable v) n (PrimState m) e 
  -> m (VGS.Vector v n e GDP.?SortedBy comp)
sortByAndFreeze (GDP.The cmp) vm@(MVector v) = do
  VAI.sortBy cmp v
  GDP.assert <$> VGS.freeze vm

--TODO do interval at type level nats? 
--(VAI.Comparison e GDP.~~ comp)
sortedInsertWholeIndexInterval :: (KnownNat n, VGB.Vector v e)
  => (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
  -> (e GDP.~~ eName)
  -> FinInterval (n + 1) GDP.?SortedInsertSearchOf comp vName eName
sortedInsertWholeIndexInterval _ e = GDP.assert 
  $ (minBound IVL.... maxBound) 

-- -> SortedInsertSearch (n + 1) e GDP.? SortedInsertSearchOf comp vecName
sortedInsertSearchAtIdx :: (KnownNat n, VGB.Vector v e) 
 => (VAI.Comparison e GDP.~~ cmp)
 -> (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
 -> (e GDP.~~ eName)
 -> F.Finite n
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName
sortedInsertSearchAtIdx (GDP.The cmp) (GDP.The v) (GDP.The e) i = GDP.assert 
  $ case cmp e (VGS.index v i) of
    GT -> (F.shift i IVL.... maxBound)
    EQ -> IVL.singleton weakI
    LT -> (minBound IVL.... weakI)
  where
    weakI = F.weaken i

sortedInsertSearchBinaryStep :: forall n v e cmp vName eName. 
 (KnownNat n, VGB.Vector v e) 
 => (VAI.Comparison e GDP.~~ cmp)
 -> (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
 -> (e GDP.~~ eName)
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName
sortedInsertSearchBinaryStep cmp v e ivlName@(GDP.The ivl)
  | IVL.singular ivl = ivlName
  | otherwise = sortedInsertSearchIntersect ivlName 
                $ sortedInsertSearchAtIdx cmp v e mi
  where
    (mi :: F.Finite n) = fromInteger 
                         $ (toInteger hi + toInteger li) `div` 2 
                         -- nb must be < n, since li < hi and hi <= n
    li = IVL.inf ivl
    hi = IVL.sup ivl


--note, element must be <= element at i, and >= element at (i - 1)
sortedInsertSearchIntersect :: KnownNat n 
 => FinInterval n GDP.? SortedInsertSearchOf cmp v e
 -> FinInterval n GDP.? SortedInsertSearchOf cmp v e
 -> FinInterval n GDP.? SortedInsertSearchOf cmp v e
sortedInsertSearchIntersect (GDP.The ivl1) (GDP.The ivl2) = GDP.assert 
  $ fromMaybe (error "Search interval intersection must be nonempty") 
  $ IVL.intersection ivl1 ivl2

sortedInsertIdxFromInterval :: KnownNat n
 => FinInterval n GDP.? SortedInsertSearchOf cmp v e
 -> Maybe (F.Finite n GDP.? SortedInsertIdx cmp v e)
sortedInsertIdxFromInterval (GDP.The ivl) 
  | IVL.singular ivl = Just . GDP.assert $ IVL.inf ivl
  | otherwise = Nothing

{-
newtype Opposite comp = Opposite Defn
type role Opposite nominal

-- A named version of the opposite ordering.
opposite :: ((a -> a -> Ordering) ~~ comp)
         -> ((a -> a -> Ordering) ~~ Opposite comp)
opposite (The comp) = defn $ \x y -> case comp x y of
  GT -> LT
  EQ -> EQ
  LT -> GT

newtype Reverse xs = Reverse Defn
type role Reverse nominal

-- A named version of Prelude's 'reverse'.
rev :: ([a] ~~ xs) -> ([a] ~~ Reverse xs)
rev (The xs) = defn (reverse xs)

-- A lemma about reversing sorted lists.
rev_ord_lemma :: SortedBy comp xs -> Proof (SortedBy (Opposite comp) (Reverse xs))
rev_ord_lemma _ = axiom
-}



