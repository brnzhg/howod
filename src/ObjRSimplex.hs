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

--TODO figure out what export
module ObjRSimplex (
  VSimplex
  , ObjRF(..)
  , ObjRVtxOf
  , ObjRVtx(..)
  , FObjRVtx(..)
  , ObjRSimplex(..)
  , SortedObjRSimplex(..)
  , CmpObjRVtx
  , makeFObjRVtx
  , cmpObjRVtx
  , RVtxObjCmp
  , getRVtxObjCmp
  ) where

import Data.Ord (comparing)
--import Data.Function (on)
--import Data.Bool (bool)
--import Data.Maybe (fromMaybe)
--import qualified Data.Foldable as FLD
import Data.Coerce

import qualified Data.Finite as F

import qualified Data.Vector.Sized as VS

import Numeric.LinearAlgebra.Static

import GHC.TypeNats

import qualified GDP

import Data.Vector.GDP.Sorted 


--TODO need another file that has SortedSimplex stuff
--must create sorted simplex with compartor that is derived from objective
--TODO problem, compartor is completely determined by ObjF in this specific case

--note this has all the axioms of Objective Simplex / Vertex, others should derive from this
--rename GDP, rename to RnObjectiveSimplex

type VSimplex v n = VS.Vector (n + 1) (v n)

type ObjRF n = R n -> ℝ

newtype ObjRVtxOf fObjName name = ObjVtxOf GDP.Defn
type role ObjRVtxOf nominal nominal

data ObjRVtx n = ObjRVtx { getX :: !(R n)
                         , getFx :: ℝ
                         }
                         deriving Show

newtype FObjRVtx fObjName n = 
  FObjRVtx { getObjRVtx :: ObjRVtx n GDP.? ObjRVtxOf fObjName }

newtype ObjRSimplex fObjName n = 
  ObjRSimplex { vtxs :: VSimplex (FObjRVtx fObjName) n }

newtype SortedObjRSimplex fObjName n =
  SortedObjRSimplex { vtxs :: VSimplex (FObjRVtx fObjName) n GDP.? SortedBy (RVtxObjCmp fObjName) }

type CmpObjRVtx fObjName n = Comparison (FObjRVtx fObjName n)


makeFObjRVtx :: (ObjRF n GDP.~~ fObjName) -> R n -> FObjRVtx fObjName n
makeFObjRVtx (GDP.The f) x = FObjRVtx $ GDP.assert ObjRVtx { getX = x, getFx = f x }


--TODO rewrite using GDP stripping proof function
--TODO note objective will be in environment, make new copy of nelderMead
cmpObjRVtx :: CmpObjRVtx fObjName n
cmpObjRVtx (FObjRVtx (GDP.The vtx1)) (FObjRVtx (GDP.The vtx2)) = 
  comparing getFx vtx1 vtx2


newtype RVtxObjCmp fObjName = RVtxObjCmp GDP.Defn
type role RVtxObjCmp nominal

getRVtxObjCmp :: (ObjRF n GDP.~~ fObjName) 
  -> (CmpObjRVtx fObjName n GDP.~~ RVtxObjCmp fObjName)
getRVtxObjCmp f = GDP.defn cmpObjRVtx


newtype VtxsOfObjRSimplex vName = VtxsOfObjRSimplex GDP.Defn
type role VtxsOfObjRSimplex nominal

getObjRSimplexNamedVtxs :: forall fObjName smplxName n. 
  ObjRSimplex fObjName n GDP.~~ smplxName
  -> (VSimplex (FObjRVtx fObjName) n GDP.~~ VtxsOfObjRSimplex smplxName)
getObjRSimplexNamedVtxs (GDP.The s) = GDP.defn $ vtxs (s :: ObjRSimplex fObjName n)