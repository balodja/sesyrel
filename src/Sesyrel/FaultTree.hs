{-# LANGUAGE OverloadedStrings, Rank2Types #-}

module Sesyrel.FaultTree (
    module Sesyrel.FaultTree.Base
  , compileDynamicFaultTree
  , compileStaticFaultTree
  , factorsLog
  , eliminationOrderLog
  , cliqueHistoryLog
  , factorsEliminate
  , factorsEliminateM
  , factorsMarginalize
  , factorsMarginalizeM
  , factorsSimpleProcess
  ) where

import Sesyrel.FaultTree.Base
import Sesyrel.FaultTree.Elimination
import Sesyrel.FaultTree.Dynamic
import Sesyrel.FaultTree.Static
import Sesyrel.Texify

import Control.Monad (forM_)
import Control.Monad.Logger
import Control.Monad.Identity (runIdentity)
import Data.List (intersperse, partition, (\\))
import Data.Monoid((<>))
import qualified Data.Text as T (pack)

noLogger :: (forall m. MonadLogger m => m a) -> a
noLogger act = runIdentity $ runNoLoggingT act

factorsLog :: (Texifiable f, MonadLogger m) => [f] -> m ()
factorsLog factors = do
  logInfoN "\\subsection{Factors}\n\n"
  let fellers = map (\f -> logInfoN (texify f <> "\n")) factors
  sequence_ (intersperse (logInfoN ",\n") fellers)
  logInfoN "\n"

factorsEliminateVariableM :: (MonadLogger m, Factor f) => Variable -> [f] -> m [f]
factorsEliminateVariableM var factors = do
  factorsLog factors
  logInfoN $ "\\subsection{Elimination of $x_{" <> texify var <> "}$}\n\n"
  let (touched, untouched) = partition (\f -> var `elem` variables f) factors
      producted = productFactors touched
  logInfoN $ texifyVariableElimination var producted <> "$= \\ldots $\n\n"
  let squeezed = eliminate var producted
  logInfoN $ "\\paragraph{Elimination result}\n" <> "$ \\ldots = $ " <> texify squeezed <> "\n\n"
  return $ squeezed : untouched

eliminationOrderLog :: MonadLogger m => [(Variable, Int)] -> m ()
eliminationOrderLog order = do
  logInfoN $ "Elimination order: " <>
    mconcat (intersperse ", " (map (texify . fst) order)) <> "\n\n"
  logInfoN . T.pack $ "Max produced clique size: " <>
    show (maximum $ map snd order) <> "\n\n"
  --logInfoN . T.pack $ "History: " <> show order <> "\n\n"

cliqueHistoryLog :: MonadLogger m => [[[Variable]]] -> m ()
cliqueHistoryLog history = do
  logInfoN . T.pack $ "Real max produced clique size: " <> show (maximum [length $ head gen | gen <- tail history]) <> "\n\n"
  logInfoN "Clique history: \n"
  forM_ history $ \cs -> logInfoN ("\\\\ $ " <> mconcat (intersperse "," $ map texify cs) <> " $\n")
  logInfoN "\n"

factorsEliminate :: Factor f => [Variable] -> Bool -> [f] -> [f]
factorsEliminate elims algo factors = noLogger (factorsEliminateM elims algo factors)

factorsEliminateM :: (Factor f, MonadLogger m) => [Variable] -> Bool -> [f] -> m [f]
factorsEliminateM elims algo factors = do
  eliminationOrderLog order
  --cliqueHistoryLog history
  go factors (map fst order)
  where
    vars = map variables factors
    history = pretend (if algo then map fst order else elims) vars
    sizes = [length $ head gen | gen <- tail history]
    order = if algo then findOrdering Nothing elims vars else zip elims sizes
    go fs [] = return fs
    go fs (v : vs) = do
              fs' <- factorsEliminateVariableM v fs
              go fs' vs

factorsMarginalize :: Factor f => [Variable] -> [f] -> [f]
factorsMarginalize margs factors = noLogger (factorsMarginalizeM margs factors)

factorsMarginalizeM :: (Factor f, MonadLogger m) => [Variable] -> [f] -> m [f]
factorsMarginalizeM margs factors =
  let vars = foldl unionVariables [] (map variables factors)
  in factorsEliminateM (vars \\ margs) True factors

factorsSimpleProcess :: (Factor f, MonadLogger m) => String -> Either [Variable] [Variable] -> [f] -> m [f]
factorsSimpleProcess name vv joint = do
  logInfoN $ "\\section{" <> T.pack name <> "}\n\n"
  marginal <- either
              (\vs -> factorsMarginalizeM vs joint)
              (\vs -> factorsEliminateM vs False joint) vv
  logInfoN "\\subsection{More elimination?}\n\n"
  constant <- factorsMarginalizeM [] marginal
  let p = productFactors constant
  logInfoN "\\subsection{Results}\n\n"
  logInfoN $ "$ F(\\infty) = $ " <> texify p <> " \n"
  return marginal
