-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.ListLen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, about lenghts of lists
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.ListLen where

import Prelude hiding (sum, length, reverse, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import qualified Data.SBV.List as SL

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)
#endif

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | Prove that the length of a list is one more than the length of its tail.
--
-- We have:
--
-- >>> runKD listLengthProof
-- Lemma: length_correct                   Q.E.D.
-- [Proven] length_correct
listLengthProof :: KD Proof
listLengthProof = do
   let length :: SList Elt -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       spec :: SList Elt -> SInteger
       spec = SL.length

       p :: SList Elt -> SBool
       p xs = observe "imp" (length xs) .== observe "spec" (spec xs)

   lemma "length_correct" (\(Forall @"xs" xs) -> p xs) [induct p]

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'listLengthProof', but with a bad implementation over integers,
-- and see the counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it. We have:
--
-- >>> runKD badProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: bad
-- *** Failed to prove bad.
-- Falsifiable. Counter-example:
--   xs   = [8,25,26,27,28,42] :: [Integer]
--   imp  =                 42 :: Integer
--   spec =                  6 :: Integer
badProof :: KD ()
badProof = do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       badLength :: SList Integer -> SInteger
       badLength xs = ite (SL.length xs .> 5 .&& 42 `SL.elem` xs) 42 (length xs)

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = observe "imp" (badLength xs) .== observe "spec" (spec xs)

   lemma "bad" (\(Forall @"xs" xs) -> p xs) [induct p]

   pure ()

-- | @length (xs ++ ys) == length xs + length ys@
--
-- We have:
--
-- >>> runKD lenAppend
-- Lemma: lenAppend                        Q.E.D.
-- [Proven] lenAppend
lenAppend :: KD Proof
lenAppend = lemma "lenAppend"
                   (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) ->
                         SL.length (xs SL.++ ys) .== SL.length xs + SL.length ys)
                   []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- We have:
--
-- >>> runKD lenAppend2
-- Lemma: lenAppend2                       Q.E.D.
-- [Proven] lenAppend2
lenAppend2 :: KD Proof
lenAppend2 = lemma "lenAppend2"
                   (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) ->
                             SL.length xs .== SL.length ys
                         .=> SL.length (xs SL.++ ys) .== 2 * SL.length xs)
                   []
