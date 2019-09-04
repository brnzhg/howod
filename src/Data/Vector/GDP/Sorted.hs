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
import Control.Monad.State.Strict
import Control.Monad.Loops (untilJust)
import Control.Arrow ((&&&))

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

--TODO alternative approach, 
--theory with IndexOfSorted i x
--theory of intervals
--lots more boilerplate

newtype SortedBy comp name = SortedBy GDP.Defn
type role SortedBy nominal nominal

newtype SortedByOf e cmp name = SortedByOf GDP.Defn
--type role SortedByOf nominal nominal nominal
--TODO figure out type role, note e is not a name

type FinInterval (n :: Nat) = IVL.Interval (F.Finite n)

--interval includes index of first element >= search element
newtype SortedInsertSearchOf cmp vName elemName searchName = SortedInsertSearchOf GDP.Defn
type role SortedInsertSearchOf nominal nominal nominal nominal

newtype SortedInsertIdx cmp vName elemName idxName = SortedInsertIdx GDP.Defn
type role SortedInsertIdx nominal nominal nominal nominal


data SortedVectorWithCmp cmpName vName v n e = SortedVectorWithCmp {
  sortedVectorCmp :: (VAI.Comparison e GDP.~~ cmpName)
  , sortedVector :: (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmpName vName)
}

--data SortedInsertSearch cmpName vName elemName searchName = SortedInsertSearch {
--  sortedVectorWithCmp :: SortedVectorWithCmp cmpName vName 
--}

--newtype MVecSorted comp v (n :: Nat) s a = MVecSorted (VGMS.MVector v n s a)

getSortedByOf :: (KnownNat n, VGB.Vector v e) 
  => (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
  -> GDP.Proof (SortedByOf e cmp vName)
getSortedByOf _ = GDP.axiom

sortByAndFreeze :: (PrimMonad m, VGB.Vector v e) 
  => (VAI.Comparison e GDP.~~ cmp)
  -> VGMS.MVector (VG.Mutable v) n (PrimState m) e 
  -> m (VGS.Vector v n e GDP.?SortedBy cmp)
sortByAndFreeze (GDP.The cmp) vm@(MVector v) = do
  VAI.sortBy cmp v
  GDP.assert <$> VGS.freeze vm

--TODO do interval at type level nats? 
--(VAI.Comparison e GDP.~~ comp)
sortedInsertWholeIndexInterval :: (KnownNat n, GDP.Fact (SortedByOf e cmp vName))
  => (e GDP.~~ eName)
  -> FinInterval (n + 1) GDP.?SortedInsertSearchOf cmp vName eName
sortedInsertWholeIndexInterval e = GDP.assert 
  $ (minBound IVL.... maxBound) 

-- -> SortedInsertSearch (n + 1) e GDP.? SortedInsertSearchOf comp vecName
sortedInsertChopAtIdx :: (KnownNat n, VGB.Vector v e) 
 => (VAI.Comparison e GDP.~~ cmp)
 -> (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
 -> (e GDP.~~ eName)
 -> F.Finite n
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName
sortedInsertChopAtIdx (GDP.The cmp) (GDP.The v) (GDP.The e) i = GDP.assert 
  $ case cmp (VGS.index v i) e of
    LT -> (F.shift i IVL.... maxBound)
    _ -> (minBound IVL.... weakI)
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
                $ sortedInsertChopAtIdx cmp v e mi
  where
    (mi :: F.Finite n) = fromMaybe (error "Bisect must be at idx < (n+1)") 
                         . F.strengthen 
                         . IVL.sup 
                         . fst 
                         . IVL.bisectIntegral 
                         $ ivl 


unsafeIntersection :: Ord a => IVL.Interval a -> IVL.Interval a -> IVL.Interval a
unsafeIntersection ivl1 ivl2=
  fromMaybe (error "Search interval intersection must be nonempty") 
  $ IVL.intersection ivl1 ivl2


--intervals contain index of first element >= search element e
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

binarySearchFromInterval :: (KnownNat n, VGB.Vector v e) 
 => (VAI.Comparison e GDP.~~ cmp)
 -> (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
 -> (e GDP.~~ eName)
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName
 -> F.Finite (n + 1) GDP.? SortedInsertIdx cmp vName eName
binarySearchFromInterval cmp v e ivl = flip evalState ivl . untilJust $ do
  modify $ sortedInsertSearchBinaryStep cmp v e
  sortedInsertIdxFromInterval <$> get

binarySearch :: forall n v e cmp vName eName. (KnownNat n, VGB.Vector v e) 
 => (VAI.Comparison e GDP.~~ cmp)
 -> (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
 -> (e GDP.~~ eName)
 -> F.Finite (n + 1) GDP.? SortedInsertIdx cmp vName eName
binarySearch cmp v e = binarySearchFromInterval cmp v e
  $ GDP.note (getSortedByOf v) $ sortedInsertWholeIndexInterval e
  --binarySearchFromInterval cmp v e $ sortedInsertWholeIndexInterval v e


sortedInsertAndShiftRight :: (KnownNat n, VGB.Vector v e)
  => (VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)
  -> F.Finite (n + 1) GDP.? SortedInsertIdx cmp vName eName
  -> (e GDP.~~ eName)
  -> VGS.Vector v n e GDP.? SortedBy cmp
sortedInsertAndShiftRight (GDP.The v) (GDP.The i) (GDP.The e) = GDP.assert
  $ case F.strengthen i of
    Nothing -> v
    Just i' -> (v VGS.//)
               $ (i', e) 
                 : [(k', VGS.index v k) | (k, k') <- uncurry zip 
                                                      . (id &&& tail) 
                                                      $ [i'..maxBound]]


--TODO need ORD

-- VGB.Vector v e
--(VGS.Vector v n e GDP.~~ vName GDP.::: SortedBy cmp vName)

sortedInsertCmpAndChop :: forall n e cmp vName eName1 eName2. KnownNat n
 => (VAI.Comparison e GDP.~~ cmp)
 -> (e GDP.~~ eName1)
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName1
 -> (e GDP.~~ eName2)
 -> FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName2
 -> (Ordering
    , FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName1
    , FinInterval (n + 1) GDP.? SortedInsertSearchOf cmp vName eName2)
sortedInsertCmpAndChop (GDP.The cmp) (GDP.The e1) (GDP.The i1) (GDP.The e2) (GDP.The i2) =
  updateIvls (cmp e1 e2) i1 i2
  where
    --ecmp = cmp e1 e2
    updateIvls EQ ivl1 ivl2 = let (ivl' :: IVL.Interval (F.Finite (n + 1))) = unsafeIntersection ivl1 ivl2
                              in (EQ, (GDP.assert ivl'), (GDP.assert ivl'))
    updateIvls LT ivl1 ivl2 = (LT
                              , (GDP.assert $ updateLowerIvl ivl1 ivl2)
                              , (GDP.assert $ updateHigherIvl ivl1 ivl2))
    updateIvls GT ivl1 ivl2 = (GT
                              , (GDP.assert $ updateHigherIvl ivl2 ivl1)
                              , (GDP.assert $ updateLowerIvl ivl2 ivl1))
    updateLowerIvl lowi highi = undefined
    updateHigherIvl lowi highi = undefined

--TODO version that just takes in one element

{-
 GDP.assert 
 $ case cmp (VGS.index v i) e of
      LT -> (F.shift i IVL.... maxBound)
    _ -> (minBound IVL.... weakI)
  where
    weakI = F.weaken i
-}

--TODO create NMSimplex modules
--(vertex ?NMVertexObj f), property of vertex to have objective
--(cmp ~~ NMObjCmp f), not a property just a name, doesnt need its own name, derived from objective since no change
                                                      
--sortedInsertBelowAndShiftLeft


--sortedInsertAtIdx

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