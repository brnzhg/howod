{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeApplications      #-}


module Main where

import Control.Monad.Primitive

import qualified Data.Vector.Sized as VS
--import Data.Vector.Algorithms.Intro as VAI

--import Neldermead
import Data.Vector.GDP.Sorted
import ObjRSimplex
import Numeric.LinearAlgebra.Static

import qualified GDP


simplexEx1 :: VSimplex R 2
simplexEx1 = VS.fromTuple (v1, v2, v3)
  where
    (v1 :: R 2) = vector [0.0, 3.0]
    (v2 :: R 2) = vector [1.0, 4.0]
    (v3 :: R 2) = vector [2.0, 0.0]

createObjSimplex :: (ObjRF n GDP.~~ fObjName) 
  -> VSimplex R n 
  -> ObjRSimplex fObjName n
createObjSimplex f = ObjRSimplex . VS.map (makeFObjRVtx f)

sortObjSimplex :: forall fObjName cmpName n m. PrimMonad m 
  => (CmpObjRVtx fObjName n GDP.~~ cmpName)
  -> ObjRSimplex fObjName n 
  -> m (SortedObjRSimplex cmpName fObjName n)
sortObjSimplex cmp smplx = do
  v <- VS.thaw $ vtxs (smplx :: ObjRSimplex fObjName n)
  SortedObjRSimplex <$> sortByAndFreeze cmp v


main :: IO ()
main = do
  GDP.name norm_1 $ \f -> 
    GDP.name cmpObjRVtx $ \c -> do
      let smplx = createObjSimplex f simplexEx1
      (SortedObjRSimplex v) <- sortObjSimplex c smplx
      putStrLn . show . VS.map (GDP.the . getObjRVtx) $ GDP.the v