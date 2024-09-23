-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.InsertionSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving insertion-sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.InsertionSort where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, length, head, tail)
import Data.SBV.List

-- | Insert an element into an already sorted list in the correct place.
insert :: SInteger -> SList Integer -> SList Integer
insert = smtFunction "insert" $ \e l -> ite (null l) (singleton e)
                                      $ let (x, xs) = uncons l
                                        in ite (e .<= x) (e .: x .: xs) (x .: insert e xs)

-- | Insertion sort, using 'insert' above to successively insert the elements.
insertionSort :: SList Integer -> SList Integer
insertionSort = smtFunction "insertionSort" $ \l -> ite (null l) nil
                                                  $ let (x, xs) = uncons l
                                                    in insert x (insertionSort xs)


-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | The default settings for z3 have trouble running this proof out-of-the-box.
-- We have to pass auto_config=false to z3!
z3NoAutoConfig :: KDConfig
z3NoAutoConfig = z3KD{kdExtraSolverArgs = ["auto_config=false"]}

-- | Correctness of insertion-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKDWith cvc5KD $ do

    insertIntoNonDecreasing1 <- lemma "insertIntoNonDecreasing1"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> e .<= x .=> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          []

    insertIntoNonDecreasing2 <- axiom "insertIntoNonDecreasing2"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> e .>  x .=> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          -- []

    insertIntoNonDecreasing3 <- lemmaWith z3KD "insertIntoNonDecreasing3"
          (\(Forall @"e" e) (Forall @"xs" xs) -> nonDecreasing xs .== nonDecreasing (insert e xs))
          [induct (\e -> nonDecreasing . insert e), insertIntoNonDecreasing1, insertIntoNonDecreasing2]

    nonDecreasingInsert <- lemma "nonDecreasingInsert"
               (\(Forall @"e" e) (Forall @"xs" xs) -> nonDecreasing xs .== nonDecreasing (insert e xs))
               [induct (\e -> nonDecreasing . insert e), insertIntoNonDecreasing3]

    lemma "insertionSortCorrect"
          (\(Forall @"l" l) -> nonDecreasing (insertionSort l))
          [induct (nonDecreasing . insertionSort), nonDecreasingInsert]
{-
    -- helper: cons isn't null
    consNotNull <- lemma "consNotNull"
                         (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) -> sNot (null (x .: xs)))
                         []

    -- helper: tail of nonDecreasing is nonDecreasing
    tlNonDec <- lemma "tailNonDec"
                      (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                      []


    insertIntoNonDecreasing2 <- chainLemma "insertIntoNonDecreasing2"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> e .> x  .=> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          (\e x xs -> [ e .> x .=> nonDecreasing (insert e (x .: xs))
                      , e .> x .=> nonDecreasing (x .: insert e xs)
                      , e .> x .=> nonDecreasing (insert e xs)
                      , e .> x .=> nonDecreasing xs
                      ])
          [induct (\e x -> nonDecreasing . insert e . (x .:)), tlNonDec]

    insertIntoNonDecreasing <- lemma "insertIntoNonDecreasing"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          [insertIntoNonDecreasing1, insertIntoNonDecreasing2, sorry]

    chainLemma "insertionSortCorrect"
               (\(Forall @"l" l) -> nonDecreasing (insertionSort l))
               (\x xs -> [ nonDecreasing (insertionSort (x .: xs))
                         , nonDecreasing (insert x (insertionSort xs))
                         , nonDecreasing (insertionSort xs)
                         ])
               [induct (nonDecreasing . insertionSort), consNotNull, insertIntoNonDecreasing]
-}
{-
    -- helper: tail of nonDecreasing is nonDecreasing
    tlNonDec <- lemma "tailNonDec"
                      (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                      []

    -- helper: inserting into a non-decreasing list leaves it non-decreasing. Insertij
    insertIntoNonDecreasing1 <- chainLemma "insertIntoNonDecreasing1"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> e .<= x .=> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          (\e x xs -> [ e .<= x .=> nonDecreasing (insert e (x .: xs))
                      , e .<= x .=> nonDecreasing (e .: x .: xs)
                      ])
          []

    insertIntoNonDecreasing2 <- chainLemma "insertIntoNonDecreasing2"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> e .> x  .=> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          (\e x xs -> [ e .> x .=> nonDecreasing (insert e (x .: xs))
                      , e .> x .=> nonDecreasing (x .: insert e xs)
                      , e .> x .=> nonDecreasing (insert e xs)
                      , e .> x .=> nonDecreasing xs
                      ])
          [induct (\e x -> nonDecreasing . insert e . (x .:)), tlNonDec ]

    insertIntoNonDecreasing <- lemma "insertIntoNonDecreasing"
          (\(Forall @"e" e) (Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .== nonDecreasing (insert e (x .: xs)))
          [insertIntoNonDecreasing1, insertIntoNonDecreasing2, sorry]

-}
