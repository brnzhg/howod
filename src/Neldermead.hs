{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Neldermead (
  Simplex(..)
  , haftkaGurdalSimplex
  ) where

import Data.Bool (bool)
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum)
import qualified Data.Foldable as FLD
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

--TODO in future, allow more flexibility in objective?
--maybe this is ok, allow objective to have writer monad
data NMVertex n = NMVertex { x :: !(R n)
                           , fx :: ℝ
                           }

newtype NMSimplex n = NMSimplex { fOrderedVertices :: V.Vector n (NMVertex n) }

newtype Simplex n = Simplex { xA :: L n (1 + n) }
    deriving (Show)

--TODO ok for these to be impossible? guess so
data BoxConstraints n = BoxConstraints
  { lb :: !(V.Vector n (Maybe ℝ))
  , ub :: !(V.Vector n (Maybe ℝ))
  }


rVecIso :: forall n. KnownNat n => LI.Iso' (R n) (SV.Vector n ℝ)
rVecIso = LI.iso rVec vecR

clampMaybe :: Ord a => Maybe a -> Maybe a -> a -> a
clampMaybe lb ub x = x''
  where
    x'' = fromMaybe x' $ min x' <$> ub
    x' = fromMaybe x $ max x <$> lb

--TODO redo to support storable
projectToBox :: forall n. KnownNat n
 => BoxConstraints n -> V.Vector n ℝ -> V.Vector n ℝ
projectToBox (BoxConstraints lb ub) = V.zipWith3 clampMaybe lb ub

{-
haftkaGurdalSimplex :: forall n. KnownNat n => ℝ -> R n -> Simplex n
haftkaGurdalSimplex size x0 = undefined
    where
      --TODO lens here, rVecIso
      (cols :: V.Vector (1 + n) (R n)) = 
        V.generate $ (\j -> x0 L.& rVecIso L.%~ (f j))
      --bob = over (rVecIso) (const x0) x0
      f :: F.Finite (1 + n) -> SV.Vector n ℝ -> SV.Vector n ℝ
      f j v = flip SV.imap v $ \i x -> x + step i j
      step i j
        | toInteger j == toInteger n' = 0
        | toInteger j == toInteger i = q + (c * l)
        | otherwise = q
      q = c * (sqrt (l + 1) - 1)
      c = size / (l * sqrt 2)
      l = fromIntegral n'
      n' = fromSing $ (sing :: Sing n)
-}

haftkaGurdalSimplex :: forall n. KnownNat n => ℝ -> R n -> Simplex n
haftkaGurdalSimplex size x0 = Simplex . colsL $ cols
    where
      (cols :: V.Vector (1 + n) (R n)) = 
        V.generate $ \j -> x0 L.& rVecIso L.%~ (SV.imap (\i x -> x + step i j))
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
