{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE FunctionalDependencies #-}

--TODO split out IsFieldOf definition into internal module
module GDP.Theory.RecordField (
  IsFieldOf(..)
  , HasNamedField(..)
  , PropHasField(..)
) where


import GDP
import GHC.TypeLits
import Data.Proxy

newtype IsFieldOf (s :: Symbol) recordName = IsFieldOf GDP.Defn


class HasNamedField (s :: Symbol) r a | s r -> a where
  getNamedField :: Proxy s -> (r ~~ recordName) -> (a ~~ IsFieldOf s recordName)

-- if uncommented this should only be used by definition modules
--getterToNamedGetter :: Defining (f recordName) => (r -> a) -> (r ~~ recordName) -> (a ~~ f recordName)
--getterToNamedGetter g = defn . g . the

class PropHasField (s :: Symbol) prop fieldName | s prop -> fieldName where
  matchPropField :: Proxy s 
    -> GDP.Proof (prop recordName) 
    -> GDP.Proof (IsFieldOf s recordName == fieldName)


