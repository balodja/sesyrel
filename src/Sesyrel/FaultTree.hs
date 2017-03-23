{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree (
    FaultTree(..)
  , FaultTreeMonad
  , evalFaultTreeMonad
  , compileDynamicFaultTree
  , evalFaultTreeStatic
  , lambdaM
  , andM, orM
  , priorityAndOrM
  , switchM
  ) where

import Sesyrel.FaultTree.Base
import Sesyrel.FaultTree.Elimination

import Sesyrel.FaultTree.Dynamic
import Sesyrel.FaultTree.Static

{-

factorsTell :: MonadLogger m => [Factor] -> m ()
factorsTell factors = do
  logInfoN "\\subsection{Factors}\n\n"
  let fellers = map (\(expr, _) -> logInfoN ("$ " <> texify expr <> " $\n")) factors
  sequence_ (intersperse (logInfoN ",\n") fellers)
  logInfoN "\n"

factorsSimpleProcess :: MonadLogger m => String -> Either [Int] [Int] -> [Factor] -> m ([Factor], Maybe (Expr Rational))
factorsSimpleProcess name vv joint = do
  logInfoN $ "\\section{" <> T.pack name <> "}\n\n"
  marginal <- either
              (\vs -> factorsMarginalize vs joint)
              (\vs -> factorsEliminate vs False joint) vv
  logInfoN "\\subsection{More elimination?}\n\n"
  constant <- factorsMarginalize [] marginal
  let p = deepExpand . foldl1 product .  map fst $ constant
  logInfoN "\\subsection{Results}\n\n"
  logInfoN $ "$ F(\\infty) = " <> texify p <> " $\n"
  distr <- case vv of
    Left [lastVar] -> do
      let marginalized = deepExpand . foldl1 product . map fst $ marginal
          mttf = fromRational $ calcMttf lastVar marginalized
          distr = calcDistribution lastVar marginalized
      logInfoN $ ", $ F(x_{" <> texify lastVar <> "}) = " <> texify distr <> "$ , $ MTTF = " <> texifyDoubleE 3 mttf <> " $\n"
      return (Just distr)
    _ -> return Nothing
  logInfoN "\n"
  return (marginal, distr)

factorsEliminate :: MonadLogger m => [Int] -> Bool -> [Factor] -> m [Factor]
factorsEliminate elims algo factors =
  do
    let order = if algo then findOrdering Nothing elims (map snd factors) else elims
    logInfoN $ "Elimination order: " <>
      mconcat (intersperse ", " (map texify order)) <> "\n\n"
    let cliques = pretend order (map snd factors)
    logInfoN "Clique history: \n"
    forM_ cliques $ \cs -> logInfoN ("\\\\ $ " <> mconcat (intersperse "," $ map texify cs) <> " $\n")
    logInfoN "\n"
    go factors order
  where
    go fs [] = return fs
    go fs (v : vs) = do
              fs' <- factorsEliminateVariable v fs
              go fs' vs

factorsMarginalize :: MonadLogger m => [Int] -> [Factor] -> m [Factor]
factorsMarginalize margs factors =
  let vars = nub . sort $ foldl union [] (map snd factors)
  in factorsEliminate (vars \\ margs) True factors

factorsEliminateVariable :: MonadLogger m => Int -> [Factor] -> m [Factor]
factorsEliminateVariable var factors = do
  factorsTell factors
  logInfoN $ "\\subsection{Integration of $x_{" <> texify var <> "}$}\n\n"
  let (varFactors, restFactors) = partition (elem var . snd) factors
      expr = ExprN (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) (map fst varFactors))
  logInfoN $ "$ " <> "\\int\\limits_0^{+\\infty} "
    <> texify expr <> "\\textrm{dx}_{" <> texify var
    <> "} = \\ldots $\n\n"
  let newExpr = integrate expr var (Constant 0) (Constant plusInfinity)
  let newVars = delete var . foldl union [] . map snd $ varFactors
  logInfoN $ "\\paragraph{Integration result}\n" <> "$ \\ldots = " <> texify newExpr <> " $\n\n"
  return $ (newExpr, newVars) : restFactors

-}