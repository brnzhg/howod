{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE DuplicateRecordFields #-}

module GDP.Theory.Order2 (

) where

import qualified Data.Ord as ORD
import Data.Function (on)
import Data.Coerce

import qualified GDP


type Comparison e = e -> e -> Ordering

newtype OrderingBy (ordering :: Ordering) a cmpName x1 x2 = OrderingBy GDP.Defn

type LtBy = OrderingBy 'LT
type EqBy = OrderingBy 'EQ
type GtBy = OrderingBy 'GT

newtype IsCmpBy a cmpName = IsCmpBy GDP.Defn

type LtEqBy a cmpName x1 x2 = (EqBy a cmpName x1 x2)
                              GDP.|| (LtBy a cmpName x1 x2)

type GtEqBy a cmpName x1 x2 = (EqBy a cmpName x1 x2) 
                              GDP.|| (GtBy a cmpName x1 x2)

type NotEqBy a cmpName x1 x2 = GDP.Not (EqBy a cmpName x1 x2)

data LtOrEq :: Ordering -> * where
    LtOrEqCaseEq :: LtOrEq 'EQ
    LtOrEqCaseLt :: LtOrEq 'LT

data GtOrEq :: Ordering -> * where
    GtOrEqCaseEq :: GtOrEq 'EQ
    GtOrEqCaseGt :: GtOrEq 'GT


cmpIsCmpBy :: Ord a => (Comparison a GDP.~~ cmpName) -> GDP.Proof (IsCmpBy a cmpName)
cmpIsCmpBy _ = GDP.axiom




instance GDP.Fact (IsCmpBy a cmpName) => GDP.Reflexive (EqBy a cmpName) where
  refl = GDP.axiom
  
instance GDP.Fact (IsCmpBy a cmpName) => GDP.Symmetric (EqBy a cmpName) where
  symmetric _ = GDP.axiom
  
instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (OrderingBy ordering a cmpName) where
  transitive _ _ = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (LtBy a cmpName) where
  irrefl = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (GtBy a cmpName) where
  irrefl = GDP.axiom



--instance GDP.Irreflexive (GtBy cmpName) where
--  irrefl = GDP.axiom 



 