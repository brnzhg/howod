{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Neldermead (
  Simplex(..)
  , haftkaGurdalSimplex
  ) where

import Data.Function (on)
import Data.Bool (bool)
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum)
import qualified Data.Foldable as FLD

import qualified Numeric.Interval.NonEmpty as IVL

import qualified Data.Finite as F
import Data.Singletons (Sing, sing, fromSing)
import Data.Singletons.TypeLits

import qualified Data.Vector.Sized as V
import qualified Data.Vector.Storable.Sized as SV
import Numeric.LinearAlgebra.Static
import Numeric.LinearAlgebra.Static.Vector
import GHC.TypeNats

import qualified Control.Lens as L
import qualified Control.Lens.Iso as LI
import qualified Control.Lens.Traversal as LT

--TODO in future - mark Vertex with the objective function
--in any constructor, must take objective and then mark it

--TODO in future, allow more flexibility in objective?
--maybe this is ok, allow objective to have writer monad
data NMVertex n = NMVertex { x :: !(R n)
                           , fx :: ℝ
                           }

newtype NMSimplex n = NMSimplex { fOrderedVertices :: V.Vector n (NMVertex n) }

newtype Simplex n = Simplex { xA :: L n (n + 1) }
    deriving (Show)

newtype BoxConstraints n = BoxConstraints { 
  unBoxConstraints :: V.Vector n (IVL.Interval ℝ)
  }
--TODO ok for these to be impossible? guess so
--data BoxConstraints n = BoxConstraints
--  { lb :: !(V.Vector n (Maybe ℝ))
--  , ub :: !(V.Vector n (Maybe ℝ))
--  }


rVecIso :: forall n. KnownNat n => LI.Iso' (R n) (SV.Vector n ℝ)
rVecIso = LI.iso rVec vecR

projectToBox :: KnownNat n => BoxConstraints n -> R n -> R n
projectToBox (BoxConstraints bc) = L.over rVecIso $ SV.imap $ IVL.clamp . V.index bc

--TODO make initial in bounds
--for each col vector (step vector, x0 is zero so sbutract x0)
--  is legal against UP, is legal against LB
--      do this by finding max negative diff
--  if both negative, take ratio of bound and current, divide whole vector

rightAngledSimplex :: forall n. KnownNat n => BoxConstraints n -> ℝ -> R n -> Simplex n
rightAngledSimplex size x0 = undefined

haftkaGurdalSimplex :: forall n. KnownNat n => ℝ -> R n -> Simplex n
haftkaGurdalSimplex size x0 = Simplex . colsL 
  $ V.generate $ \j -> x0 L.& rVecIso L.%~ (SV.imap (\i x -> x + step i j))
  where
    step i j
      | toInteger j == toInteger n' = 0
      | toInteger j == toInteger i = q + (c * l)
      | otherwise = q
    q = c * (sqrt (l + 1) - 1)
    c = size / (l * sqrt 2)
    l = fromIntegral n'
    n' = fromSing $ (sing :: Sing n)


centroid :: forall n t. (KnownNat n, Foldable t) => t (R n) -> R n
centroid = (/l) . FLD.foldl' (+) 0
  where
    l = fromIntegral . fromSing $ (sing :: Sing n)


centroidL :: forall m n. (KnownNat m, KnownNat n) => L m n -> R m
centroidL = (#> (1.0 / l))
  where
    l = fromIntegral . fromSing $ (sing :: Sing m)

--TODO write version using mean
--toRows, map mean, list to vec
centroidL2 :: forall m n. Sing m -> Sing n -> L m n -> R m
centroidL2 (sm@SNat) (sn@SNat) = (#> (1.0 / l))
  where
    l = fromIntegral . fromSing $ (sing :: Sing m)

realWithinRelTol :: ℝ -> ℝ -> ℝ -> Bool
realWithinRelTol relTol x y = (<= 0.5 * (x `absAdd` y)) . abs $ x - y
  where absAdd = (+) `on` abs

realWithinTols :: Maybe ℝ -> Maybe ℝ -> ℝ -> ℝ -> Bool
realWithinTols relTol absTol x y = relTolCheck && absTolCheck 
  where 
    relTolCheck = fromMaybe True 
      $ (\t -> realWithinRelTol t x y) <$> relTol
    absTolCheck = fromMaybe True $ (<= abs (x - y)) <$> absTol


--center + max step to given vertex for each dimension
simplexRadiusTo :: KnownNat n => Simplex n -> R n -> R n
simplexRadiusTo (Simplex xs) c = vecR $ SV.generate (V.index v)
  where 
    v = (SV.maximum . rVec) <$> lRows xsDiff -- Vector, need to convert to (R n)
    xsDiff = xs - (c `outer` 1) -- vector not promoted to matrix

affineCombWith :: KnownNat n => R n -> ℝ -> R n -> R n
affineCombWith x cy y = x + rnScale cy (y - x)

--put in helper class, maybe use coerce or something
rnScale :: KnownNat n => ℝ -> R n -> R n
rnScale c = L.over rVecIso $ SV.map (c *)
--affinecombwithclamp
--anchor, x, combweight, bounds
--anchor + weight * (x - anchor)