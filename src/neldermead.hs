{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import Data.Bool (bool)
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum)
import qualified Data.Foldable as FLD
import qualified Data.Finite as F
import Data.Singletons (Sing, sing, fromSing)
import Data.Singletons.TypeLits

import qualified Data.Vector.Sized as V
import Numeric.LinearAlgebra.Static
import GHC.TypeNats

--TODO in future, allow more flexibility in objective?
--maybe this is ok, allow objective to have writer monad
data NMVertex n = NMVertex { x :: !(R n)
                           , fx :: ℝ
                           }

newtype NMSimplex n = NMSimplex { fOrderedVertices :: V.Vector n (NMVertex n) }

newtype Simplex n = Simplex { xA :: L n (1 + n) }

data BoxConstraints n = BoxConstraints
  { lb :: !(V.Vector n (Maybe ℝ))
  , ub :: !(V.Vector n (Maybe ℝ))
  }


clampMaybe :: Ord a => Maybe a -> Maybe a -> a -> a
clampMaybe lb ub x = x''
  where
    x'' = fromMaybe x' $ min x' <$> ub
    x' = fromMaybe x $ max x <$> lb

projectToBox :: forall n. KnownNat n
  => BoxConstraints n -> V.Vector n ℝ -> V.Vector n ℝ
projectToBox (BoxConstraints lb ub) = V.zipWith3 clampMaybe lb ub


haftkaGurdalSimplex :: forall n. KnownNat n => ℝ -> R n -> Simplex n
haftkaGurdalSimplex size x0 = Simplex
  $ col x0 ||| build (\i j -> bool pMinQ 0 (i == j))
  where
    pMinQ = c * l
    q = c * (sqrt (l + 1) - 1)
    c = size / (l * sqrt 2)
    l = fromIntegral . fromSing $ (sing :: Sing n)



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
