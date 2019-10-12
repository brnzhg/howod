{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE FlexibleContexts      #-}

module GDP.Theory.VectorBasic (
  IsVector
  , IthOfVec
  , IsIthOfVec
  , vectorIsVector
  , getIthOfVector
  , matchNameIthOfVec
  , unnameIthOfVec
) where

import Data.Ord
import Data.Function (on)

import qualified Data.Finite as F

import qualified Data.Vector.Generic.Sized as VGS
import qualified Data.Vector.Generic.Base as VGB

import GHC.TypeNats

import qualified GDP


newtype IsVector (n :: Nat) e vecName = IsVector GDP.Defn
type role IsVector representational representational nominal

newtype IthOfVec vecName idxName = IthOfVector GDP.Defn
type role IthOfVec nominal nominal

newtype IsIthOfVec vecName idxName elemName = IsIthOfVec GDP.Defn
type role IsIthOfVec nominal nominal nominal

vectorIsVector :: (KnownNat n, VGB.Vector v e)
  => (VGS.Vector v n e GDP.~~ vName) 
  -> GDP.Proof (IsVector n e vName)
vectorIsVector _ = GDP.axiom

getIthOfVector :: (KnownNat n, VGB.Vector v e)
  => (VGS.Vector v n e GDP.~~ vName)
  -> (F.Finite n GDP.~~ idxName)
  -> (e GDP.~~ IthOfVec vName idxName)
getIthOfVector (GDP.The v) (GDP.The i) = GDP.defn $ VGS.index v i


matchNameIthOfVec :: GDP.Fact (IsIthOfVec vName idxName elemName)
  => GDP.Proof (IthOfVec vName idxName GDP.== elemName)
matchNameIthOfVec = GDP.axiom

unnameIthOfVec :: (e GDP.~~ IthOfVec vName idxName) -> (e GDP.? IsIthOfVec vName idxName)
unnameIthOfVec = GDP.assert . GDP.the

--TODO could be generic typeclass, nameablePredicate
--p is a name, coercible
--q is prop, * -> *, and (q a) is coercible, see ? to see how to write this
-- x ~~ p -> x ? q
--- GDP.Fact q b => GDP.Proof (p == b)

{- 
newtype IsIthOfVector vecName ithName = IsIthOfVector GDP.Defn
type role IsIthOfVector nominal nominal

newtype XiOfVector ithName = XiOfVector GDP.Defn
type role XiOfVector nominal

--private, only way to create is fetch from vector
--equality of index implies equality
data IthOfVector (n :: Nat) e = IthOfVector {
    i :: F.Finite n
    , x :: e
}

getIthOfVector :: (KnownNat n, VGB.Vector v e)
  => (VGS.Vector v n e GDP.~~ vName) 
  -> F.Finite n 
  -> (IthOfVector n e GDP.? IsIthOfVector vName)
getIthOfVector (GDP.The v) i = GDP.assert $ IthOfVector {
    i = i
    , x = VGS.index v i
  }

getXiOfVector :: (IthOfVector n e GDP.~~ ithName) -> (e GDP.~~ XiOfVector ithName)
getXiOfVector = GDP.defn . x . GDP.the
-}


