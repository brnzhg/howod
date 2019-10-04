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


module GDP.Theory.TotalPreorderOrd (
  OrdCmp
  , OrdLtEqBy
  , OrdGtEqBy
  , OrdEqBy
  , OrdLtBy
  , OrdGtBy
  , getOrdCmp
  ) where

import qualified Data.Ord as ORD
import Data.Coerce
import qualified Data.Proxy as Proxy

import qualified GDP
import GDP.Theory.TotalPreorder


newtype OrdCmp proxyName = OrdCmp GDP.Defn
type role OrdCmp nominal

type OrdLtEqBy p x1 x2 = LtEqBy (OrdCmp p) x1 x2
type OrdGtEqBy p x1 x2 = GtEqBy (OrdCmp p) x1 x2
type OrdEqBy p x1 x2 = EqBy (OrdCmp p) x1 x2
type OrdLtBy p x1 x2 = LtBy (OrdCmp p) x1 x2
type OrdGtBy p x1 x2 = GtBy (OrdCmp p) x1 x2


getOrdCmp :: Ord a => (Proxy.Proxy a GDP.~~ p) -> (Comparison a GDP.~~ OrdCmp p)
getOrdCmp _ = GDP.defn $ ORD.compare



