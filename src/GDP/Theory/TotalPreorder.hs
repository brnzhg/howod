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

--TODO name Total Preorder since we allow for ties
module GDP.Theory.TotalPreorder (

) where

import qualified Data.Ord as ORD
import Data.Function (on)
import Data.Coerce

import Control.Arrow ((&&&))

import qualified GDP


type Comparison e = e -> e -> Ordering

newtype LtEqBy a cmpName x1 x2 = LtEqBy GDP.Defn

type GtEqBy a cmpName x1 x2 = LtEqBy a cmpName x2 x1
type EqBy a cmpName x1 x2 = (LtEqBy a cmpName x1 x2)
                            GDP.&& (GtEqBy a cmpName x1 x2)

type LtBy a cmpName x1 x2 = (LtEqBy a cmpName x1 x2)
                            GDP.&& (GDP.Not (GtEqBy a cmpName x1 x2))

type GtBy a cmpName x1 x2 = (GtEqBy a cmpName x1 x2)
                            GDP.&& (GDP.Not (LtEqBy a cmpName x1 x2))

newtype IsCmpBy a cmpName = IsCmpBy GDP.Defn


data CmpByCase a cmpName x1 x2 = 
  EqByCase (GDP.Proof (EqBy a cmpName x1 x2)) 
  | LtByCase (GDP.Proof (LtBy a cmpName x1 x2))
  | GtByCase (GDP.Proof (GtBy a cmpName x1 x2))

classify :: (Comparison a GDP.~~ cmpName) 
  -> (a GDP.~~ x1Name) 
  -> (a GDP.~~ x2Name) 
  -> CmpByCase a cmpName x1Name x2Name
classify (GDP.The cmp) (GDP.The x1) (GDP.The x2) = case cmp x1 x2 of
  EQ -> EqByCase GDP.axiom
  LT -> LtByCase GDP.axiom
  GT -> GtByCase GDP.axiom

cmpIsCmpBy :: (Comparison a GDP.~~ cmpName) -> GDP.Proof (IsCmpBy a cmpName)
cmpIsCmpBy _ = GDP.axiom

ltEqByRefl :: GDP.Fact (IsCmpBy a cmpName) 
  => (a GDP.~~ xName) 
  -> GDP.Proof (LtEqBy a cmpName xName xName)
ltEqByRefl _ = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (LtEqBy a cmpName) where
  transitive _ _ = GDP.axiom

--nb derived
gtEqByRefl :: GDP.Fact (IsCmpBy a cmpName) 
  => (a GDP.~~ xName) 
  -> GDP.Proof (GtEqBy a cmpName xName xName)
gtEqByRefl = ltEqByRefl

eqByRefl :: GDP.Fact (IsCmpBy a cmpName) 
  => (a GDP.~~ xName)  
  -> GDP.Proof (EqBy a cmpName xName xName)
eqByRefl x = GDP.introAnd (ltEqByRefl x) (ltEqByRefl x)

eqBySymmetric :: GDP.Fact (IsCmpBy a cmpName)
  => GDP.Proof (EqBy a cmpName x1 x2)
  -> GDP.Proof (EqBy a cmpName x2 x1)
eqBySymmetric = GDP.symmetric

eqByTransitive :: GDP.Fact (IsCmpBy a cmpName)
  => GDP.Proof (EqBy a cmpName x1 x2)
  -> GDP.Proof (EqBy a cmpName x2 x3)
  -> GDP.Proof (EqBy a cmpName x1 x3)
eqByTransitive p1 p2 = 
  GDP.introAnd (GDP.transitive pl1 pl2) (GDP.transitive pr2 pr1)
  where
    (pl1, pr1) = (GDP.elimAndL &&& GDP.elimAndR) p1
    (pl2, pr2) = (GDP.elimAndL &&& GDP.elimAndR) p2

-- mutual exclusive proofs
ltByNotGtEq :: GDP.Fact (IsCmpBy a cmpName)
  => GDP.Proof (LtBy a cmpName x1 x2)
  -> GDP.Proof (GDP.Not (GtEqBy a cmpName x1 x2))
ltByNotGtEq = GDP.elimAndR

gtByNotLtEq :: GDP.Fact (IsCmpBy a cmpName)
  => GDP.Proof (GtBy a cmpName x1 x2)
  -> GDP.Proof (GDP.Not (LtEqBy a cmpName x1 x2))
gtByNotLtEq = ltByNotGtEq

eqByNotLtGt :: forall a cmpName x1 x2. (GDP.Classical, GDP.Fact (IsCmpBy a cmpName))
  => GDP.Proof (EqBy a cmpName x1 x2)
  -> GDP.Proof ((GDP.Not (LtBy a cmpName x1 x2)) GDP.&& (GDP.Not (GtBy a cmpName x1 x2)))
eqByNotLtGt eqpf =  GDP.introAnd notLtByPf notGtByPf
  where 
    notLtByPf :: GDP.Proof (GDP.Not (LtBy a cmpName x1 x2))
    notLtByPf = deMorgansFactorNotOr . GDP.introOrR . introNotNot . GDP.elimAndR  $ eqpf
    notGtByPf :: GDP.Proof (GDP.Not (GtBy a cmpName x1 x2))
    notGtByPf = deMorgansFactorNotOr . GDP.introOrR . introNotNot . GDP.elimAndL $ eqpf


ltByTransitiveL :: forall a cmpName x1 x2 x3. (GDP.Classical, GDP.Fact (IsCmpBy a cmpName))
  => GDP.Proof ((LtBy a cmpName x1 x2) GDP.&& (LtEqBy a cmpName x2 x3))
  -> GDP.Proof (LtBy a cmpName x1 x3)
ltByTransitiveL p = GDP.introAnd ltEqByPf13 $ GDP.elimOr case2Eq3 case2Lt3 GDP.lem 
  where
    ltEqByPf13 :: GDP.Proof (LtEqBy a cmpName x1 x3)
    ltEqByPf13 = GDP.transitive (GDP.elimAndL pl) pr
    case2Eq3Helper :: GDP.Proof (GtEqBy a cmpName x2 x3) -> GDP.Proof (GtEqBy a cmpName x1 x3) -> GDP.Proof (EqBy a cmpName x1 x2)
    case2Eq3Helper gtEqPf23 gtEqPf13 = eqByTransitive (GDP.introAnd ltEqByPf13 gtEqPf13) . eqBySymmetric $ GDP.introAnd pr gtEqPf23
    case2Eq3 :: GDP.Proof (GtEqBy a cmpName x2 x3) -> GDP.Proof (GDP.Not (GtEqBy a cmpName x1 x3))--GDP.Proof (LtBy a cmpName x1 x3)
    case2Eq3 gtEqPf23 = GDP.introNot (\gtEqPf13 -> GDP.contradicts (GDP.elimAndR $ case2Eq3Helper gtEqPf23 gtEqPf13) (GDP.elimAndR pl))
    case2Lt3 :: GDP.Proof (GDP.Not (GtEqBy a cmpName x2 x3)) -> GDP.Proof (GDP.Not (GtEqBy a cmpName x1 x3))
    case2Lt3 notGtEqPf23 = GDP.introNot (\gtEqPf13 -> flip GDP.contradicts notGtEqPf23 $ GDP.transitive gtEqPf13 (GDP.elimAndL pl))
    (pl, pr) = (GDP.elimAndL &&& GDP.elimAndR) p




deMorgansDistrNotAnd :: GDP.Classical
  => GDP.Proof (GDP.Not (p GDP.And q)) 
  -> GDP.Proof ((GDP.Not p) GDP.|| (GDP.Not q))
deMorgansDistrNotAnd _ = GDP.axiom

deMorgansDistrNotOr :: GDP.Classical
  => GDP.Proof (GDP.Not (p GDP.Or q)) 
  -> GDP.Proof ((GDP.Not p) GDP.&& (GDP.Not q))
deMorgansDistrNotOr _ = GDP.axiom

deMorgansFactorNotOr :: GDP.Classical
  => GDP.Proof ((GDP.Not p) GDP.|| (GDP.Not q)) 
  -> GDP.Proof (GDP.Not (p GDP.&& q))
deMorgansFactorNotOr _ = GDP.axiom

deMorgansFactorNotAnd :: GDP.Classical
  => GDP.Proof ((GDP.Not p) GDP.&& (GDP.Not q))
  -> GDP.Proof (GDP.Not (p GDP.|| q))
deMorgansFactorNotAnd _ = GDP.axiom

introNotNot :: GDP.Proof p -> GDP.Proof (GDP.Not (GDP.Not p))
introNotNot = GDP.introNot . GDP.contradicts


--ltByIrrefl :: GDP.Fact (IsCmpBy a cmpName) 
-- => GDP.Proof (length)

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Symmetric (EqBy a cmpName) where
--symmetric _ = GDP.axiom

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Reflexive (EqBy a cmpName) where
--refl = GDP.axiom
  
--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Symmetric (EqBy a cmpName) where
--symmetric _ = GDP.axiom
  
--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (EqBy a cmpName) where
--transitive _ _ = GDP.axiom

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (LtBy a cmpName) where
--irrefl = GDP.axiom

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (LtBy a cmpName) where
--transitive _ _ = GDP.axiom

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (GtBy a cmpName) where
--irrefl = GDP.axiom 

--instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (GtBy a cmpName) where
--transitive _ _ = GDP.axiom

--instance GDP.Fact (LtEqBy a cmpName) => GDP.Transitive (LtEqBy a cmpName) where
--transitive ()
 