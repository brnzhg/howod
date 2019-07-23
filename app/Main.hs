{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import Neldermead

import Numeric.LinearAlgebra.Static


main :: IO ()
main = do
    let (v :: R 4) = vector [0.0, 0.0, 0.0, 0.0]
    putStrLn . show $ haftkaGurdalSimplex 1.0 v

