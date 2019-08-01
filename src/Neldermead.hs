{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Neldermead (
  Simplex(..)
  , haftkaGurdalSimplex
  ) where

import Data.Ord (comparing)
import Data.Function (on)
import Data.Bool (bool)
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum)
import qualified Data.Foldable as FLD
import qualified Data.Proxy as PXY
import Data.Coerce

import Control.Arrow ((&&&))
import Control.Monad.State.Strict

import qualified Numeric.Interval.NonEmpty as IVL

import qualified Data.Finite as F
import Data.Singletons (Sing, sing, fromSing)
import Data.Singletons.TypeLits

import qualified Data.Vector.Sized as V
import qualified Data.Vector.Storable.Sized as SV
--import qualified Data.Vector.Mutable.Sized as MV
import Numeric.LinearAlgebra.Static
import Numeric.LinearAlgebra.Static.Vector
import GHC.TypeNats

import qualified Control.Lens as L
import qualified Control.Lens.Iso as LI
import qualified Control.Lens.Traversal as LT

--TODO in future - mark Vertex with the objective function
--in any constructor, must take objective and then mark it

--TODO in future, allow more flexibility in objective?
--TODO better field names or allow overloaded
--TODO lenses
data NMVertex n = NMVertex { getX :: !(R n)
                           , getFx :: ℝ
                           }

newtype NMSimplex n = NMSimplex { fOrderedVertices :: V.Vector (n + 1) (NMVertex n) }

newtype Simplex n = Simplex { xA :: L n (n + 1) }
    deriving (Show)

newtype BoxConstraints n = BoxConstraints { unBoxConstraints :: V.Vector n (IVL.Interval ℝ) }

data NMScalars = NMScalars {
  reflectWeight :: ℝ
  , expandWeight :: ℝ
  , contractWeight :: ℝ
  , shrinkWeight :: ℝ
}

--TODO convergeTest should be monadic to allow writing details
--
data NMEnv n = MEnv {
  scalars :: NMScalars
  , simplexConvergeTest :: NMSimplex n -> Bool
}

newtype OnBounds = OnBounds { unOnBounds :: Bool }

makeNMVertex :: KnownNat n => (R n -> ℝ) -> R n -> NMVertex n
makeNMVertex f x = NMVertex { getX = x, getFx = f x }

nextNMSimplex :: forall n. (KnownNat n, 1 <= n) 
  => NMScalars -> (R n -> ℝ) -> NMSimplex n -> NMSimplex n
nextNMSimplex env f (NMSimplex vtxs)
  | comparing getFx vtxReflect vtxl == LT = undefined --expand case
  | comparing getFx vtxReflect vtxl2 == LT = undefined -- just keep swap out reflect and re-order
  | otherwise = undefined --shrink case
  where
    vtxl = V.head vtxs
    vtxl2 = V.index vtxs $ F.natToFinite (PXY.Proxy @1)
    vtxh = V.last vtxs
    xc = centroid $ getX <$> FLD.toList vtxs
    vtxReflect = makeNMVertex f $ affineCombWith (getX vtxh) (reflectWeight env) xc



--TODO may need MonadReader and MonadState, and allow objective to be in any monad
rVecIso :: KnownNat n => LI.Iso' (R n) (SV.Vector n ℝ)
rVecIso = LI.iso rVec vecR

projectToBox :: KnownNat n => BoxConstraints n -> R n -> R n
projectToBox (BoxConstraints bc) = 
  L.over rVecIso $ SV.imap $ IVL.clamp . V.index bc

-- Return bool is weather any dimension was clamped
projectToBoxState :: KnownNat n 
  => BoxConstraints n -> R n -> State OnBounds (R n)
projectToBoxState (BoxConstraints bc) = L.mapMOf rVecIso 
  $ SV.imapM $ \i x -> do
    let bci = V.index bc i
    modify $ coerce (|| x `IVL.notMember` bci)
    return $ IVL.clamp bci x


--awkward because cant deconstruct interval into inf sup
--and cant zip storable and not storable
rightAngledSimplexInBox :: forall n. KnownNat n 
  => BoxConstraints n -> R n -> R n -> Simplex n
rightAngledSimplexInBox (BoxConstraints bc) step x0 = Simplex
  $ ((x0 `outer` 1) + diag step') ||| col x0
  where
    (step' :: R n) = vecR
      $ SV.generate
      $ \i -> let stepBounds = V.index bc i - IVL.singleton (SV.index vx0 i)
                  si = abs $ SV.index vstep i
              in clampStep ((IVL.inf &&& IVL.sup) stepBounds) si
    clampStep (stepLb, stepUb) stepi 
      | stepi <= stepUb = stepi
      | -stepi >= stepLb = -stepi
      | -stepLb < stepUb = max 0 $ 0.5 * stepUb
      | otherwise = min 0 $ 0.5 * stepLb
    vstep = rVec step
    vx0 = rVec x0
    

haftkaGurdalSimplex :: forall n. KnownNat n => ℝ -> R n -> Simplex n
haftkaGurdalSimplex size x0 = Simplex . colsL 
  $ V.generate $ \j -> x0 L.& rVecIso L.%~ (SV.imap $ \i x -> x + step i j)
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


realWithinRelTol :: ℝ -> ℝ -> ℝ -> Bool
realWithinRelTol relTol x y = (<= 0.5 * (x `absAdd` y)) . abs $ x - y
  where absAdd = (+) `on` abs

realWithinTols :: Maybe ℝ -> Maybe ℝ -> ℝ -> ℝ -> Bool
realWithinTols relTol absTol x y = relTolCheck && absTolCheck 
  where 
    relTolCheck = fromMaybe True 
      $ (\t -> realWithinRelTol t x y) <$> relTol
    absTolCheck = fromMaybe True $ (<= abs (x - y)) <$> absTol


simplexRadiusTo :: (KnownNat n, Foldable t) => t (R n) -> R n -> R n
simplexRadiusTo xs c = vecR 
  $ SV.generate 
  $ \i -> FLD.foldl' (\acc -> (max `on` abs) acc . distci i . rVec) 0 xs
  where 
    distci i v = SV.index v i - SV.index vc i
    vc = rVec c


--center + max step to given vertex for each dimension
simplexRadiusToL :: KnownNat n => Simplex n -> R n -> R n
simplexRadiusToL (Simplex xs) c = vecR $ SV.generate (V.index v)
  where 
    v = (SV.maximumBy (comparing abs) . rVec) <$> lRows xsDiff -- Vector, need to convert to (R n)
    xsDiff = xs - (c `outer` 1) -- vector not promoted to matrix

affineCombWith :: KnownNat n => R n -> ℝ -> R n -> R n
affineCombWith x cy y = x + rnScale cy (y - x)

--put in helper class, maybe use coerce or something
rnScale :: KnownNat n => ℝ -> R n -> R n
rnScale c = L.over rVecIso $ SV.map (c *)


--TODO write version using mean
--toRows, map mean, list to vec
centroidL2 :: forall m n. Sing m -> Sing n -> L m n -> R m
centroidL2 (sm@SNat) (sn@SNat) = (#> (1.0 / l))
  where
    l = fromIntegral . fromSing $ (sing :: Sing m)

