-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Arrays.InitVals
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing arrays with initializers
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Arrays.InitVals(tests) where

import Utils.SBVTestFramework

readDef :: Predicate
readDef = do c :: SInteger <- free "c"
             i :: SInteger <- free "i"
             j <- free "j"
             let a = lambdaArray (const c)

             let a' = writeArray a j 32

             return $ ite (i ./= j) (readArray a' i .== c)
                                    (readArray a' i .== 32)

readNoDef :: Predicate
readNoDef = do i :: SInteger <- free "i"
               j :: SInteger <- free "j"

               a <- sArray_

               return $ readArray a i .== j

constArr :: Predicate
constArr = do i :: SInteger <- sInteger "i"
              j :: SInteger <- sInteger "j"

              constrain $ i .< j
              constrain $ i `sElem` [1, 2, 3, 75]
              pure $ readArray myArray i .== readArray myArray j
  where myArray = listArray [(1, 12), (2, 5) , (3, 6), (75, 5)] (7 :: Integer)

constArr2 :: Predicate
constArr2 = do i :: SInteger <- sInteger "i"
               j :: SInteger <- sInteger "j"

               constrain $ i .< j
               constrain $ i `sElem` [1, 2, 3, 75]
               pure $ readArray myArray i .== readArray myArray j
  where myArray = listArray [(1, 12), (2, 5) , (3, 6), (75, 5)] (2 :: Integer)

tests :: TestTree
tests =
  testGroup "Arrays.InitVals"
    [ testCase "readDef_SArray"              $ assertIsThm readDef
    , testCase "readDef2_SArray2"            $ assertIsSat readNoDef
    , goldenCapturedIO "constArr_SArray"     $ t
    , goldenCapturedIO "constArr2_SArray"    $ t2
    ]
    where t  goldFile = do r <- satWith defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile} constArr
                           appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")
          t2 goldFile = do r <- satWith defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile} constArr2
                           appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

{- HLint ignore module "Reduce duplication" -}
