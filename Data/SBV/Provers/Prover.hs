-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.Prover
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate
       , ProvableM(..), Provable, SatisfiableM(..), Satisfiable, Reducible
       , generateSMTBenchmark
       , Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , isVacuous, isVacuousWith
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , abc, boolector, bitwuzla, cvc4, cvc5, dReal, mathSAT, yices, z3, defaultSMTCfg, defaultDeltaSMTCfg
       ) where

import Control.Monad          (when, unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.DeepSeq        (rnf, NFData(..))

import Control.Concurrent.Async (async, waitAny, asyncThreadId, Async, mapConcurrently)
import Control.Exception (finally, throwTo)
import System.Exit (ExitCode(ExitSuccess))

import System.IO.Unsafe (unsafeInterleaveIO)             -- only used safely!

import System.Directory  (getCurrentDirectory)
import Data.Time (getZonedTime, NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.List (intercalate, isPrefixOf)

import Data.Maybe (mapMaybe, listToMaybe)

import qualified Data.Foldable   as S (toList)
import qualified Data.Text       as T

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.SMT.Utils (debug, alignPlain)
import Data.SBV.Utils.ExtractIO
import Data.SBV.Utils.TDiff

import qualified Data.SBV.Trans.Control as Control
import qualified Data.SBV.Control.Query as Control
import qualified Data.SBV.Control.Utils as Control

import GHC.Stack

import qualified Data.SBV.Provers.ABC       as ABC
import qualified Data.SBV.Provers.Boolector as Boolector
import qualified Data.SBV.Provers.Bitwuzla  as Bitwuzla
import qualified Data.SBV.Provers.CVC4      as CVC4
import qualified Data.SBV.Provers.CVC5      as CVC5
import qualified Data.SBV.Provers.DReal     as DReal
import qualified Data.SBV.Provers.MathSAT   as MathSAT
import qualified Data.SBV.Provers.Yices     as Yices
import qualified Data.SBV.Provers.Z3        as Z3

import GHC.TypeLits

mkConfig :: SMTSolver -> SMTLibVersion -> [Control.SMTOption] -> SMTConfig
mkConfig s smtVersion startOpts = SMTConfig { verbose                     = False
                                            , timing                      = NoTiming
                                            , printBase                   = 10
                                            , printRealPrec               = 16
                                            , crackNum                    = False
                                            , transcript                  = Nothing
                                            , solver                      = s
                                            , smtLibVersion               = smtVersion
                                            , dsatPrecision               = Nothing
                                            , extraArgs                   = []
                                            , satCmd                      = "(check-sat)"
                                            , satTrackUFs                 = True                   -- i.e., yes, do extract UI function values
                                            , allSatMaxModelCount         = Nothing                -- i.e., return all satisfying models
                                            , allSatPrintAlong            = False                  -- i.e., do not print models as they are found
                                            , isNonModelVar               = const False            -- i.e., everything is a model-variable by default
                                            , validateModel               = False
                                            , optimizeValidateConstraints = False
                                            , roundingMode                = RoundNearestTiesToEven
                                            , solverSetOptions            = startOpts
                                            , ignoreExitCode              = False
                                            , redirectVerbose             = Nothing
                                            }

-- | If supported, this makes all output go to stdout, which works better with SBV
-- Alas, not all solvers support it..
allOnStdOut :: Control.SMTOption
allOnStdOut = Control.DiagnosticOutputChannel "stdout"

-- | Default configuration for the ABC synthesis and verification tool.
abc :: SMTConfig
abc = mkConfig ABC.abc SMTLib2 [allOnStdOut]

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector SMTLib2 []

-- | Default configuration for the Bitwuzla SMT solver
bitwuzla :: SMTConfig
bitwuzla = mkConfig Bitwuzla.bitwuzla SMTLib2 []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 SMTLib2 [allOnStdOut]

-- | Default configuration for the CVC5 SMT Solver.
cvc5 :: SMTConfig
cvc5 = mkConfig CVC5.cvc5 SMTLib2 [allOnStdOut]

-- | Default configuration for the Yices SMT Solver.
dReal :: SMTConfig
dReal = mkConfig DReal.dReal SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                                     ]

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT SMTLib2 [allOnStdOut]

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices SMTLib2 []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                            , allOnStdOut
                            ]

-- | The default solver used by SBV. This is currently set to z3.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = z3

-- | The default solver used by SBV for delta-satisfiability problems. This is currently set to dReal,
-- which is also the only solver that supports delta-satisfiability.
defaultDeltaSMTCfg :: SMTConfig
defaultDeltaSMTCfg = dReal

-- | A predicate is a symbolic program that returns a (symbolic) boolean value. For all intents and
-- purposes, it can be treated as an n-ary function from symbolic-values to a boolean. The 'Symbolic'
-- monad captures the underlying representation, and can/should be ignored by the users of the library,
-- unless you are building further utilities on top of SBV itself. Instead, simply use the 'Predicate'
-- type when necessary.
type Predicate = Symbolic SBool

-- | A goal is a symbolic program that returns no values. The idea is that the constraints/min-max
-- goals will serve as appropriate directives for sat/prove calls.
type Goal = Symbolic ()

-- | A class of values that can be "provided" as an argument to turn it into a predicate
class ReducibleM m a where
  -- | Turn a value into a predicate, by providing an parameter as argument.
  argReduce :: a -> SymbolicT m SBool

-- | `Reducible` is specialization of `ReducibleM` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Reducible = ReducibleM IO

-- | A type @a@ is provable if we can turn it into a predicate that can be proven.
class ExtractIO m => ProvableM m a where
  -- | Generalization of 'Data.SBV.prove'
  prove :: a -> m ThmResult

  default prove :: ReducibleM m a => a -> m ThmResult
  prove = proveWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.proveWith'
  proveWith :: SMTConfig -> a -> m ThmResult

  default proveWith :: ReducibleM m a => SMTConfig -> a -> m ThmResult
  proveWith cfg a = do r <- runWithQuery False (checkNoOptimizations >> Control.getSMTResult) cfg a
                       ThmResult <$> if validationRequested cfg
                                     then validate False cfg a r
                                     else return r

  -- | Generalization of 'Data.SBV.dprove'
  dprove :: a -> m ThmResult

  default dprove :: ReducibleM m a => a -> m ThmResult
  dprove = dproveWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.dproveWith'
  dproveWith :: SMTConfig -> a -> m ThmResult

  default dproveWith :: ReducibleM m a => SMTConfig -> a -> m ThmResult
  dproveWith cfg a = do r <- runWithQuery False (checkNoOptimizations >> Control.getSMTResult) cfg a
                        ThmResult <$> if validationRequested cfg
                                      then validate False cfg a r
                                      else return r

  -- | Generalization of 'Data.SBV.isTheorem'
  isTheorem :: a -> m Bool
  isTheorem = isTheoremWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isTheoremWith'
  isTheoremWith :: SMTConfig -> a -> m Bool
  isTheoremWith cfg p = do r <- proveWith cfg p
                           let bad = error $ "SBV.isTheorem: Received:\n" ++ show r
                           case r of
                             ThmResult Unsatisfiable{} -> return True
                             ThmResult Satisfiable{}   -> return False
                             ThmResult DeltaSat{}      -> return False
                             ThmResult SatExtField{}   -> return False
                             ThmResult Unknown{}       -> bad
                             ThmResult ProofError{}    -> bad

  -- | Prove a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  proveWithAll :: [SMTConfig] -> a -> m [(Solver, NominalDiffTime, ThmResult)]
  proveWithAll  = (`sbvWithAll` proveWith)

  -- | Prove a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send an exception to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  proveWithAny :: [SMTConfig] -> a -> m (Solver, NominalDiffTime, ThmResult)
  proveWithAny  = (`sbvWithAny` proveWith)

  -- | Prove a property by running many queries each isolated to their own thread
  -- concurrently and return the first that finishes, killing the others
  proveConcurrentWithAny :: SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, ThmResult)

  default proveConcurrentWithAny :: ReducibleM m a => SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, ThmResult)
  proveConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                          return (slvr, time, ThmResult result)
    where go cfg a' q = runWithQuery False (do _ <- q;  checkNoOptimizations >> Control.getSMTResult) cfg a'

  -- | Prove a property by running many queries each isolated to their own thread
  -- concurrently and wait for each to finish returning all results
  proveConcurrentWithAll :: SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, ThmResult)]

  default proveConcurrentWithAll :: ReducibleM m a => SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, ThmResult)]
  proveConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                          return $ (\(a',b,c) -> (a',b,ThmResult c)) <$> results
    where go cfg a' q = runWithQuery False (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | A type @a@ can be used in sat calls  if we can turn it into a predicate that can be satisfied
class ExtractIO m => SatisfiableM m a where
  -- | Generalization of 'Data.SBV.sat'
  sat :: a -> m SatResult

  default sat :: ReducibleM m a => a -> m SatResult
  sat = satWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  satWith :: SMTConfig -> a -> m SatResult

  default satWith :: ReducibleM m a => SMTConfig -> a -> m SatResult
  satWith cfg a = do r <- runWithQuery True (checkNoOptimizations >> Control.getSMTResult) cfg a
                     SatResult <$> if validationRequested cfg
                                   then validate True cfg a r
                                   else return r

  -- | Generalization of 'Data.SBV.sat'
  dsat :: a -> m SatResult
  dsat = dsatWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  dsatWith :: SMTConfig -> a -> m SatResult

  default dsatWith :: ReducibleM m a => SMTConfig -> a -> m SatResult
  dsatWith cfg a = do r <- runWithQuery True (checkNoOptimizations >> Control.getSMTResult) cfg a
                      SatResult <$> if validationRequested cfg
                                    then validate True cfg a r
                                    else return r

  -- | Generalization of 'Data.SBV.allSat'
  allSat :: a -> m AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.allSatWith'
  allSatWith :: SMTConfig -> a -> m AllSatResult

  default allSatWith :: ReducibleM m a => SMTConfig -> a -> m AllSatResult
  allSatWith cfg a = do asr <- runWithQuery True (checkNoOptimizations >> Control.getAllSatResult) cfg a
                        if validationRequested cfg
                           then do rs' <- mapM (validate True cfg a) (allSatResults asr)
                                   return asr{allSatResults = rs'}
                           else return asr

  -- | Generalization of 'Data.SBV.isSatisfiable'
  isSatisfiable :: a -> m Bool

  default isSatisfiable :: ReducibleM m a => a -> m Bool
  isSatisfiable = isSatisfiableWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isSatisfiableWith'
  isSatisfiableWith :: SMTConfig -> a -> m Bool

  default isSatisfiableWith :: ReducibleM m a => SMTConfig -> a -> m Bool
  isSatisfiableWith cfg p = do r <- satWith cfg p
                               case r of
                                 SatResult Satisfiable{}   -> return True
                                 SatResult Unsatisfiable{} -> return False
                                 _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

  -- | Generalization of 'Data.SBV.optimize'
  optimize :: OptimizeStyle -> a -> m OptimizeResult

  default optimize :: ReducibleM m a => OptimizeStyle -> a -> m OptimizeResult
  optimize = optimizeWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.optimizeWith'
  optimizeWith :: SMTConfig -> OptimizeStyle -> a -> m OptimizeResult

  default optimizeWith :: ReducibleM m a => SMTConfig -> OptimizeStyle -> a -> m OptimizeResult
  optimizeWith config style optGoal = do
                   res <- runWithQuery True opt config optGoal
                   if not (optimizeValidateConstraints config)
                      then return res
                      else let v :: SMTResult -> m SMTResult
                               v = validate True config optGoal
                           in case res of
                                LexicographicResult m -> LexicographicResult <$> v m
                                IndependentResult xs  -> let w []            sofar = return (reverse sofar)
                                                             w ((n, m):rest) sofar = v m >>= \m' -> w rest ((n, m') : sofar)
                                                         in IndependentResult <$> w xs []
                                ParetoResult (b, rs)  -> ParetoResult . (b, ) <$> mapM v rs

    where opt = do objectives <- Control.getObjectives

                   when (null objectives) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: Unsupported call to optimize when no objectives are present."
                                          , "*** Use \"sat\" for plain satisfaction"
                                          ]

                   unless (supportsOptimization (capabilities (solver config))) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: The backend solver " ++ show (name (solver config)) ++ "does not support optimization goals."
                                          , "*** Please use a solver that has support, such as z3"
                                          ]

                   when (validateModel config && not (optimizeValidateConstraints config)) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: Model validation is not supported in optimization calls."
                                          , "***"
                                          , "*** Instead, use `cfg{optimizeValidateConstraints = True}`"
                                          , "***"
                                          , "*** which checks that the results satisfy the constraints but does"
                                          , "*** NOT ensure that they are optimal."
                                          ]


                   let optimizerDirectives = concatMap minmax objectives ++ priority style
                         where mkEq (x, y) = "(assert (= " ++ show x ++ " " ++ show y ++ "))"

                               minmax (Minimize          _  xy@(_, v))     = [mkEq xy, "(minimize "    ++ show v                 ++ ")"]
                               minmax (Maximize          _  xy@(_, v))     = [mkEq xy, "(maximize "    ++ show v                 ++ ")"]
                               minmax (AssertWithPenalty nm xy@(_, v) mbp) = [mkEq xy, "(assert-soft " ++ show v ++ penalize mbp ++ ")"]
                                 where penalize DefaultPenalty    = ""
                                       penalize (Penalty w mbGrp)
                                          | w <= 0         = error $ unlines [ "SBV.AssertWithPenalty: Goal " ++ show nm ++ " is assigned a non-positive penalty: " ++ shw
                                                                             , "All soft goals must have > 0 penalties associated."
                                                                             ]
                                          | True           = " :weight " ++ shw ++ maybe "" group mbGrp
                                          where shw = show (fromRational w :: Double)

                                       group g = " :id " ++ g

                               priority Lexicographic = [] -- default, no option needed
                               priority Independent   = ["(set-option :opt.priority box)"]
                               priority (Pareto _)    = ["(set-option :opt.priority pareto)"]

                   mapM_ (Control.send True) optimizerDirectives

                   case style of
                     Lexicographic -> LexicographicResult <$> Control.getLexicographicOptResults
                     Independent   -> IndependentResult   <$> Control.getIndependentOptResults (map objectiveName objectives)
                     Pareto mbN    -> ParetoResult        <$> Control.getParetoOptResults mbN

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  satWithAll :: [SMTConfig] -> a -> m [(Solver, NominalDiffTime, SatResult)]

  default satWithAll :: ReducibleM m a => [SMTConfig] -> a -> m [(Solver, NominalDiffTime, SatResult)]
  satWithAll = (`sbvWithAll` satWith)

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send an exception to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  satWithAny :: [SMTConfig] -> a -> m (Solver, NominalDiffTime, SatResult)

  default satWithAny :: ReducibleM m a => [SMTConfig] -> a -> m (Solver, NominalDiffTime, SatResult)
  satWithAny = (`sbvWithAny` satWith)

  -- | Find a satisfying assignment to a property using a single solver, but
  -- providing several query problems of interest, with each query running in a
  -- separate thread and return the first one that returns. This can be useful to
  -- use symbolic mode to drive to a location in the search space of the solver
  -- and then refine the problem in query mode. If the computation is very hard to
  -- solve for the solver than running in concurrent mode may provide a large
  -- performance benefit.
  satConcurrentWithAny :: SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, SatResult)

  default satConcurrentWithAny :: ReducibleM m a => SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, SatResult)
  satConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                        return (slvr, time, SatResult result)
    where go cfg a' q = runWithQuery True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

  -- | Find a satisfying assignment to a property using a single solver, but run
  -- each query problem in a separate isolated thread and wait for each thread to
  -- finish. See 'satConcurrentWithAny' for more details.
  satConcurrentWithAll :: SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, SatResult)]

  default satConcurrentWithAll :: ReducibleM m a => SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, SatResult)]
  satConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                        return $ (\(a',b,c) -> (a',b,SatResult c)) <$> results
    where go cfg a' q = runWithQuery True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Generalization of 'Data.SBV.isVacuous'
isVacuous :: (ReducibleM m a, ExtractIO m) => a -> m Bool
isVacuous = isVacuousWith defaultSMTCfg

-- | Generalization of 'Data.SBV.isVacuousWith'
isVacuousWith :: forall a m. (ReducibleM m a, ExtractIO m) =>SMTConfig -> a -> m Bool
isVacuousWith cfg a = -- NB. Can't call runWithQuery since last constraint would become the implication!
     fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup True cfg) (argReduce a >> Control.executeQuery QueryInternal check)
   where
     check :: QueryT m Bool
     check = do cs <- Control.checkSat
                case cs of
                  Control.Unsat  -> return True
                  Control.Sat    -> return False
                  Control.DSat{} -> return False
                  Control.Unk    -> error "SBV: isVacuous: Solver returned unknown!"

-- | Validate a model obtained from the solver
validate :: (ReducibleM m a, MonadIO m) => Bool -> SMTConfig -> a -> SMTResult -> m SMTResult
validate isSAT cfg p res = case res of
                             Unsatisfiable{} -> return res
                             Satisfiable _ m -> case modelBindings m of
                                                  Nothing  -> error "Data.SBV.validate: Impossible happened; no bindings generated during model validation."
                                                  Just env -> check env

                             DeltaSat {}     -> cant [ "The model is delta-satisfiable."
                                                     , "Cannot validate delta-satisfiable models."
                                                     ]

                             SatExtField{}   -> cant [ "The model requires an extension field value."
                                                     , "Cannot validate models with infinities/epsilons produced during optimization."
                                                     , ""
                                                     , "To turn validation off, use `cfg{optimizeValidateConstraints = False}`"
                                                     ]

                             Unknown{}       -> return res
                             ProofError{}    -> return res

  where cant msg = return $ ProofError cfg (msg ++ [ ""
                                                   , "Unable to validate the produced model."
                                                   ]) (Just res)

        check env = do let envShown = showModelDictionary True True cfg modelBinds
                              where modelBinds = [(T.unpack n, RegularCV v) | (NamedSymVar _ n, v) <- env]

                           notify s
                             | not (verbose cfg) = return ()
                             | True              = debug cfg ["[VALIDATE] " `alignPlain` s]

                       notify $ "Validating the model. " ++ if null env then "There are no assignments." else "Assignment:"
                       mapM_ notify ["    " ++ l | l <- lines envShown]

                       result <- snd <$> runSymbolic cfg (Concrete (Just (isSAT, env))) (argReduce p >>= output)

                       let explain  = [ ""
                                      , "Assignment:"  ++ if null env then " <none>" else ""
                                      ]
                                   ++ [ ""          | not (null env)]
                                   ++ [ "    " ++ l | l <- lines envShown]
                                   ++ [ "" ]

                           wrap tag extras = return $ ProofError cfg (tag : explain ++ extras) (Just res)

                           giveUp   s     = wrap ("Data.SBV: Cannot validate the model: " ++ s)
                                                 [ "SBV's model validator is incomplete, and cannot handle this particular case."
                                                 , "Please report this as a feature request or possibly a bug!"
                                                 ]

                           badModel s     = wrap ("Data.SBV: Model validation failure: " ++ s)
                                                 [ "Backend solver returned a model that does not satisfy the constraints."
                                                 , "This could indicate a bug in the backend solver, or SBV itself. Please report."
                                                 ]

                           notConcrete sv = wrap ("Data.SBV: Cannot validate the model, since " ++ show sv ++ " is not concretely computable.")
                                                 (  perhaps (why sv)
                                                 ++ [ "SBV's model validator is incomplete, and cannot handle this particular case."
                                                    , "Please report this as a feature request or possibly a bug!"
                                                    ]
                                                 )
                                where perhaps Nothing  = []
                                      perhaps (Just x) = [x, ""]

                                      -- This is incomplete, but should capture the most common cases
                                      why s = case s `lookup` S.toList (pgmAssignments (resAsgns result)) of
                                                Nothing            -> Nothing
                                                Just (SBVApp o as) -> case o of
                                                                        Uninterpreted v   -> Just $ "The value depends on the uninterpreted constant " ++ show v ++ "."
                                                                        QuantifiedBool _  -> Just "The value depends on a quantified variable."
                                                                        IEEEFP FP_FMA     -> Just "Floating point FMA operation is not supported concretely."
                                                                        IEEEFP _          -> Just "Not all floating point operations are supported concretely."
                                                                        OverflowOp _      -> Just "Overflow-checking is not done concretely."
                                                                        _                 -> listToMaybe $ mapMaybe why as

                           cstrs = S.toList $ resConstraints result

                           walkConstraints [] cont = do
                              unless (null cstrs) $ notify "Validated all constraints."
                              cont
                           walkConstraints ((isSoft, attrs, sv) : rest) cont
                              | kindOf sv /= KBool
                              = giveUp $ "Constraint tied to " ++ show sv ++ " is non-boolean."
                              | isSoft || sv == trueSV
                              = walkConstraints rest cont
                              | sv == falseSV
                              = case mbName of
                                  Just nm -> badModel $ "Named constraint " ++ show nm ++ " evaluated to False."
                                  Nothing -> badModel "A constraint was violated."
                              | True
                              = notConcrete sv
                              where mbName = listToMaybe [n | (":named", n) <- attrs]

                           -- SAT: All outputs must be true
                           satLoop []
                             = do notify "All outputs are satisfied. Validation complete."
                                  return res
                           satLoop (sv:svs)
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | sv == trueSV
                             = satLoop svs
                             | sv == falseSV
                             = badModel "Final output evaluated to False."
                             | True
                             = notConcrete sv

                           -- Proof: At least one output must be false
                           proveLoop [] somethingFailed
                             | somethingFailed = do notify "Counterexample is validated."
                                                    return res
                             | True            = do notify "Counterexample violates none of the outputs."
                                                    badModel "Counter-example violates no constraints."
                           proveLoop (sv:svs) somethingFailed
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | sv == trueSV
                             = proveLoop svs somethingFailed
                             | sv == falseSV
                             = proveLoop svs True
                             | True
                             = notConcrete sv

                           -- Output checking is tricky, since we behave differently for different modes
                           checkOutputs []
                             | null cstrs
                             = giveUp "Impossible happened: There are no outputs nor any constraints to check."
                           checkOutputs os
                             = do notify "Validating outputs."
                                  if isSAT then satLoop   os
                                           else proveLoop os False

                       notify $ if null cstrs
                                then "There are no constraints to check."
                                else "Validating " ++ show (length cstrs) ++ " constraint(s)."

                       walkConstraints cstrs (checkOutputs (resOutputs result))

-- | `Provable` is specialization of `ProvableM` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Provable = ProvableM IO

-- | `Data.SBV.Provers.Satisfiable` is specialization of `SatisfiableM` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Satisfiable = SatisfiableM IO

-- | Create an SMT-Lib2 benchmark. The 'Bool' argument controls whether this is a SAT instance, i.e.,
-- translate the query directly, or a PROVE instance, i.e., translate the negated query.
generateSMTBenchmark :: (MonadIO m, ReducibleM m a, SatisfiableM m a) => Bool -> a -> m String
generateSMTBenchmark isSat a = do
      t <- liftIO getZonedTime

      let comments = ["Automatically created by SBV on " ++ show t]
          cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

      (_, res) <- runSymbolic cfg (SMTMode QueryInternal ISetup isSat cfg) $ argReduce a >>= output

      let SMTProblem{smtLibPgm} = Control.runProofOn (SMTMode QueryInternal IRun isSat cfg) QueryInternal comments res
          out                   = show (smtLibPgm cfg)

      return $ out ++ "\n(check-sat)\n"

checkNoOptimizations :: MonadIO m => QueryT m ()
checkNoOptimizations = do objectives <- Control.getObjectives

                          unless (null objectives) $
                                error $ unlines [ ""
                                                , "*** Data.SBV: Unsupported call sat/prove when optimization objectives are present."
                                                , "*** Use \"optimize\"/\"optimizeWith\" to calculate optimal satisfaction!"
                                                ]

-- Custom instance of satisfiability for goals. We don't want to define a ReducibleM instance
-- as otherwise we end up with Goal being, provable; which is very confusing.
instance ExtractIO m => SatisfiableM m (SymbolicT m ()) where
  sat                        a = sat                        (a >> pure sTrue)
  satWith              cfg   a = satWith              cfg   (a >> pure sTrue)
  dsat                       a = dsat                       (a >> pure sTrue)
  dsatWith             cfg   a = dsatWith             cfg   (a >> pure sTrue)
  allSat                     a = allSat                     (a >> pure sTrue)
  allSatWith           cfg   a = allSatWith           cfg   (a >> pure sTrue)
  isSatisfiable              a = isSatisfiable              (a >> pure sTrue)
  isSatisfiableWith    cfg   a = isSatisfiableWith    cfg   (a >> pure sTrue)
  optimize                 s a = optimize                 s (a >> pure sTrue)
  optimizeWith         cfg s a = optimizeWith         cfg s (a >> pure sTrue)
  satWithAll           cfg   a = satWithAll           cfg   (a >> pure sTrue)
  satWithAny           cfg   a = satWithAny           cfg   (a >> pure sTrue)
  satConcurrentWithAny cfg s a = satConcurrentWithAny cfg s (a >> pure sTrue)
  satConcurrentWithAll cfg s a = satConcurrentWithAll cfg s (a >> pure sTrue)

-- | Create a fresh argument
mkArg :: (SymVal a, MonadSymbolic m) => m (SBV a)
mkArg = mkSymVal (NonQueryVar Nothing) Nothing

-- Simple booleans
instance Applicative m => ReducibleM m SBool where
  argReduce = pure

-- Computation producing a bool
instance ReducibleM m (SymbolicT m SBool) where
  argReduce = id

-- Universal
instance (Monad m, Constraint Symbolic r, SymVal a) => ReducibleM m (Forall a -> r) where
  argReduce = argReduce . quantifiedBool

-- Existential
instance (Monad m, Constraint Symbolic r, SymVal a) => ReducibleM m (Exists a -> r) where
  argReduce = argReduce . quantifiedBool

-- Multi universal
instance (Monad m, Constraint Symbolic r, SymVal a, KnownNat n) => ReducibleM m (ForallN n a -> r) where
  argReduce = argReduce . quantifiedBool

-- Multi existential
instance (Monad m, Constraint Symbolic r, SymVal a, KnownNat n) => ReducibleM m (ExistsN n a -> r) where
  argReduce = argReduce . quantifiedBool

-- Functions
instance (MonadIO m, ReducibleM m r, SymVal a) => ReducibleM m (SBV a -> r) where
  argReduce k = mkArg >>= argReduce . k

-- Arrays
instance (MonadIO m, ReducibleM m r, SymVal a, HasKind b) => ReducibleM m (SArray a b -> r) where
  argReduce k = newArray_ Nothing >>= argReduce . k

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b) => ReducibleM m ((SBV a, SBV b) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b -> k (a, b)

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b, SymVal c) => ReducibleM m ((SBV a, SBV b, SBV c) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c -> k (a, b, c)

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b, SymVal c, SymVal d) => ReducibleM m ((SBV a, SBV b, SBV c, SBV d) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d -> k (a, b, c, d)

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b, SymVal c, SymVal d, SymVal e) => ReducibleM m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e -> k (a, b, c, d, e)

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f) => ReducibleM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e f -> k (a, b, c, d, e, f)

instance (MonadIO m, ReducibleM m r, SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g) => ReducibleM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e f g -> k (a, b, c, d, e, f, g)

-- ProvableM/SatisfiableM instances
{- NOTE THAT the following instances are not defined on purpose:
     instance ProvableM     m (SymbolicT m ()) -- We don't want prove to be called with just constraints. It's confusing
     instance ProvableM     m Bool             -- Allows bad things like (Note ==, not .==): prove $ \x y -> x == (y :: SWord8)
     instance SatisifiableM m Bool             -- Allows bad things like (Note ==, not .==): sat   $ \x y -> x == (y :: SWord8)
-}
instance ExtractIO m                                                     => ProvableM    m SBool
instance ExtractIO m                                                     => ProvableM    m (SymbolicT m SBool)
instance (ProvableM m r, Constraint Symbolic r, SymVal a)                => ProvableM    m (Forall    a -> r)
instance (ProvableM m r, Constraint Symbolic r, SymVal a)                => ProvableM    m (Exists    a -> r)
instance (ProvableM m r, Constraint Symbolic r, SymVal a, KnownNat n)    => ProvableM    m (ForallN n a -> r)
instance (ProvableM m r, Constraint Symbolic r, SymVal a, KnownNat n)    => ProvableM    m (ExistsN n a -> r)
instance (ProvableM m r, ReducibleM m r,        SymVal a, HasKind b)     => ProvableM    m (SArray a b  -> r)

instance ExtractIO m                                                     => SatisfiableM m SBool
instance ExtractIO m                                                     => SatisfiableM m (SymbolicT m SBool)
instance (SatisfiableM m r, Constraint Symbolic r, SymVal a)             => SatisfiableM m (Forall    a -> r)
instance (SatisfiableM m r, Constraint Symbolic r, SymVal a)             => SatisfiableM m (Exists    a -> r)
instance (SatisfiableM m r, Constraint Symbolic r, SymVal a, KnownNat n) => SatisfiableM m (ForallN n a -> r)
instance (SatisfiableM m r, Constraint Symbolic r, SymVal a, KnownNat n) => SatisfiableM m (ExistsN n a -> r)

instance (ProvableM m r,    ReducibleM m r, SymVal a)                                                               => ProvableM    m (SBV a                                             -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b)                                                    => ProvableM    m ((SBV a, SBV b)                                    -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b, SymVal c)                                          => ProvableM    m ((SBV a, SBV b, SBV c)                             -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d)                                => ProvableM    m ((SBV a, SBV b, SBV c, SBV d)                      -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e)                      => ProvableM    m ((SBV a, SBV b, SBV c, SBV d, SBV e)               -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e, SymVal f)            => ProvableM    m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f)        -> r)
instance (ProvableM m r,    ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g)  => ProvableM    m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a)                                                               => SatisfiableM m (SBV a                                             -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b)                                                    => SatisfiableM m ((SBV a, SBV b)                                    -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b, SymVal c)                                          => SatisfiableM m ((SBV a, SBV b, SBV c)                             -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d)                                => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d)                      -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e)                      => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e)               -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e, SymVal f)            => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f)        -> r)
instance (SatisfiableM m r, ReducibleM m r, SymVal a, SymVal  b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g)  => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r)

-- | Generalization of 'Data.SBV.runSMT'
runSMT :: MonadIO m => SymbolicT m a -> m a
runSMT = runSMTWith defaultSMTCfg

-- | Generalization of 'Data.SBV.runSMTWith'
runSMTWith :: MonadIO m => SMTConfig -> SymbolicT m a -> m a
runSMTWith cfg a = fst <$> runSymbolic cfg (SMTMode QueryExternal ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: (ExtractIO m, ReducibleM m a) => Bool -> QueryT m b -> SMTConfig -> a -> m b
runWithQuery isSAT q cfg a = fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup isSAT cfg) comp
  where comp =  do _ <- argReduce a >>= output
                   Control.executeQuery QueryInternal q

-- | Check if a safe-call was safe or not, turning a 'SafeResult' to a Bool.
isSafe :: SafeResult -> Bool
isSafe (SafeResult (_, _, result)) = case result of
                                       Unsatisfiable{} -> True
                                       Satisfiable{}   -> False
                                       DeltaSat{}      -> False   -- conservative
                                       SatExtField{}   -> False   -- conservative
                                       Unknown{}       -> False   -- conservative
                                       ProofError{}    -> False   -- conservative

-- | Perform an action asynchronously, returning results together with diff-time.
runInThread :: NFData b => UTCTime -> (SMTConfig -> m b) -> SMTConfig -> IO (Async (Solver, NominalDiffTime, b))
runInThread beginTime action config = async $ do
                result  <- extractIO $ action config
                endTime <- rnf result `seq` getCurrentTime
                return (name (solver config), endTime `diffUTCTime` beginTime, result)

-- | Perform action for all given configs, return the first one that wins. Note that we do
-- not wait for the other asyncs to terminate; hopefully they'll do so quickly.
sbvWithAny :: (MonadIO m, NFData b) => [SMTConfig] -> (SMTConfig -> a -> m b) -> a -> m (Solver, NominalDiffTime, b)
sbvWithAny []      _    _ = error "SBV.withAny: No solvers given!"
sbvWithAny solvers what a = liftIO $ do beginTime <- getCurrentTime
                                        snd `fmap` (mapM (runInThread beginTime (`what` a)) solvers >>= waitAnyFastCancel)
   where -- Async's `waitAnyCancel` nicely blocks; so we use this variant to ignore the
         -- wait part for killed threads.
         waitAnyFastCancel asyncs = waitAny asyncs `finally` mapM_ cancelFast asyncs
         cancelFast other = throwTo (asyncThreadId other) ExitSuccess


sbvConcurrentWithAny :: (MonadIO m, NFData c) => SMTConfig -> (SMTConfig -> a -> QueryT m b -> m c) -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, c)
sbvConcurrentWithAny solver what queries a = liftIO $ snd `fmap` (mapM runQueryInThread queries >>= waitAnyFastCancel)
  where  -- Async's `waitAnyCancel` nicely blocks; so we use this variant to ignore the
         -- wait part for killed threads.
         waitAnyFastCancel asyncs = waitAny asyncs `finally` mapM_ cancelFast asyncs
         cancelFast other = throwTo (asyncThreadId other) ExitSuccess
         runQueryInThread q = do beginTime <- getCurrentTime
                                 runInThread beginTime (\cfg -> what cfg a q) solver

sbvConcurrentWithAll :: (MonadIO m, NFData c) => SMTConfig -> (SMTConfig -> a -> QueryT m b -> m c) -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, c)]
sbvConcurrentWithAll solver what queries a = liftIO (mapConcurrently runQueryInThread queries  >>= unsafeInterleaveIO . go)
  where  runQueryInThread q =liftIO $ do beginTime <- getCurrentTime
                                         runInThread beginTime (\cfg -> what cfg a q) solver

         go []  = return []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     return (r : rs)

-- | Perform action for all given configs, return all the results.
sbvWithAll :: (MonadIO m, NFData b) => [SMTConfig] -> (SMTConfig -> a -> m b) -> a -> m [(Solver, NominalDiffTime, b)]
sbvWithAll solvers what a = liftIO $ do beginTime <- getCurrentTime
                                        mapM (runInThread beginTime (`what` a)) solvers >>= (unsafeInterleaveIO . go)
   where go []  = return []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     return (r : rs)

-- | Symbolically executable program fragments. This class is mainly used for 'safe' calls, and is sufficiently populated internally to cover most use
-- cases. Users can extend it as they wish to allow 'safe' checks for SBV programs that return/take types that are user-defined.
class ExtractIO m => SExecutable m a where
   -- | Generalization of 'Data.SBV.sName'
   sName :: a -> SymbolicT m ()

   -- | Generalization of 'Data.SBV.safe'
   safe :: a -> m [SafeResult]
   safe = safeWith defaultSMTCfg

   -- | Generalization of 'Data.SBV.safeWith'
   safeWith :: SMTConfig -> a -> m [SafeResult]
   safeWith cfg a = do cwd <- (++ "/") <$> liftIO getCurrentDirectory
                       let mkRelative path
                              | cwd `isPrefixOf` path = drop (length cwd) path
                              | True                  = path
                       fst <$> runSymbolic cfg (SMTMode QueryInternal ISafe True cfg) (sName a >> check mkRelative)
     where check :: (FilePath -> FilePath) -> SymbolicT m [SafeResult]
           check mkRelative = Control.executeQuery QueryInternal $ Control.getSBVAssertions >>= mapM (verify mkRelative)

           -- check that the cond is unsatisfiable. If satisfiable, that would
           -- indicate the assignment under which the 'Data.SBV.sAssert' would fail
           verify :: (FilePath -> FilePath) -> (String, Maybe CallStack, SV) -> QueryT m SafeResult
           verify mkRelative (msg, cs, cond) = do
                   let locInfo ps = let loc (f, sl) = concat [mkRelative (srcLocFile sl), ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f]
                                    in intercalate ",\n " (map loc ps)
                       location   = (locInfo . getCallStack) `fmap` cs

                   result <- do Control.push 1
                                Control.send True $ "(assert " ++ show cond ++ ")"
                                r <- Control.getSMTResult
                                Control.pop 1
                                return r

                   return $ SafeResult (location, msg, result)

instance (ExtractIO m, NFData a) => SExecutable m (SymbolicT m a) where
   sName a = a >>= \r -> rnf r `seq` return ()

instance ExtractIO m => SExecutable m (SBV a) where
   sName v = sName (output v :: SymbolicT m (SBV a))

-- Unit output
instance ExtractIO m => SExecutable m () where
   sName () = sName (output () :: SymbolicT m ())

-- List output
instance ExtractIO m => SExecutable m [SBV a] where
   sName vs = sName (output vs :: SymbolicT m [SBV a])

-- 2 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b) => SExecutable m (SBV a, SBV b) where
  sName (a, b) = sName (output a >> output b :: SymbolicT m (SBV b))

-- 3 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c) => SExecutable m (SBV a, SBV b, SBV c) where
  sName (a, b, c) = sName (output a >> output b >> output c :: SymbolicT m (SBV c))

-- 4 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d) => SExecutable m (SBV a, SBV b, SBV c, SBV d) where
  sName (a, b, c, d) = sName (output a >> output b >> output c >> output c >> output d :: SymbolicT m (SBV d))

-- 5 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName (a, b, c, d, e) = sName (output a >> output b >> output c >> output d >> output e :: SymbolicT m (SBV e))

-- 6 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName (a, b, c, d, e, f) = sName (output a >> output b >> output c >> output d >> output e >> output f :: SymbolicT m (SBV f))

-- 7 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f, NFData g, SymVal g) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName (a, b, c, d, e, f, g) = sName (output a >> output b >> output c >> output d >> output e >> output f >> output g :: SymbolicT m (SBV g))

-- Functions
instance (SymVal a, SExecutable m p) => SExecutable m (SBV a -> p) where
   sName k = mkArg >>= \a -> sName $ k a

-- 2 Tuple input
instance (SymVal a, SymVal b, SExecutable m p) => SExecutable m ((SBV a, SBV b) -> p) where
  sName k = mkArg >>= \a -> sName $ \b -> k (a, b)

-- 3 Tuple input
instance (SymVal a, SymVal b, SymVal c, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c -> k (a, b, c)

-- 4 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d -> k (a, b, c, d)

-- 5 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e -> k (a, b, c, d, e)

-- 6 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e f -> k (a, b, c, d, e, f)

-- 7 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e f g -> k (a, b, c, d, e, f, g)

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
