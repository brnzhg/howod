{-# LANGUAGE TypeOperators         #-}

module GDP.Theory.ClassicalExtras (
    deMorgansDistrNotAnd
    , deMorgansDistrNotOr
    , deMorgansFactorNotOr
    , deMorgansFactorNotAnd
    , introNotNot
  ) where

import GDP


deMorgansDistrNotAnd :: Classical 
  => Proof (Not (p And q)) -> Proof ((Not p) || (Not q))
deMorgansDistrNotAnd _ = axiom

deMorgansDistrNotOr :: Classical
  => Proof (Not (p Or q)) -> Proof ((Not p) && (Not q))
deMorgansDistrNotOr _ = axiom

deMorgansFactorNotOr :: Classical
  => Proof ((Not p) || (Not q)) 
  -> Proof (Not (p && q))
deMorgansFactorNotOr _ = axiom

deMorgansFactorNotAnd :: Classical
  => Proof ((Not p) && (Not q))
  -> Proof (Not (p || q))
deMorgansFactorNotAnd _ = axiom

introNotNot :: Proof p -> Proof (Not (Not p))
introNotNot = introNot . contradicts


