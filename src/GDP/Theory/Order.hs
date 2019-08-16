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
module GDP.Theory.Order (

) where

import qualified Data.Ord as ORD
import Data.Function (on)
import Data.Coerce

import qualified GDP


type Comparison e = e -> e -> Ordering

newtype EqBy a cmpName x1 x2 = EqBy GDP.Defn
newtype LtBy a cmpName x1 x2 = LtBy GDP.Defn
newtype GtBy a cmpName x1 x2 = GtBy GDP.Defn

newtype IsCmpBy a cmpName = IsCmpBy GDP.Defn

type LtEqBy a cmpName x1 x2 = (LtBy a cmpName x1 x2) GDP.|| (EqBy a cmpName x1 x2)
type GtEqBy a cmpName x1 x2 = (GtBy a cmpName x1 x2) GDP.|| (EqBy a cmpName x1 x2)
type LtGtBy a cmpName x1 x2 = (LtBy a cmpName x1 x2) GDP.|| (GtBy a cmpName x1 x2)

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

--sameIsSameBy :: Ord a => (Comparison a GDP.~~ cmpName) 
-- -> (a GDP.~~ xName) 
-- -> (a GDP.~~ xName) 
-- -> GDP.Proof (EqBy cmpName xName xName)

-- (GDP.Fact (IsCmpBy cmpName)) 
instance GDP.Fact (IsCmpBy a cmpName) => GDP.Reflexive (EqBy a cmpName) where
  refl = GDP.axiom
  
instance GDP.Fact (IsCmpBy a cmpName) => GDP.Symmetric (EqBy a cmpName) where
  symmetric _ = GDP.axiom
  
instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (EqBy a cmpName) where
  transitive _ _ = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (LtBy a cmpName) where
  irrefl = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (LtBy a cmpName) where
  transitive _ _ = GDP.axiom

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Irreflexive (GtBy a cmpName) where
  irrefl = GDP.axiom 

instance GDP.Fact (IsCmpBy a cmpName) => GDP.Transitive (GtBy a cmpName) where
  transitive _ _ = GDP.axiom

--instance GDP.Fact (LtEqBy a cmpName) => GDP.Transitive (LtEqBy a cmpName) where
--transitive ()
 