{-# LANGUAGE RecursiveDo, FlexibleContexts #-}

import Expression

import qualified Data.Set as S
import Data.List (partition, union, delete)

import Control.Monad.RWS
import Control.Monad.Writer
import Control.Monad.Fix

import Control.Monad (forM_)

type FaultTreeM = RWS Int [String] FaultTree

data FaultTree = FaultTree {
    faultTreeVariables :: Int
  , faultTreeFactors :: [Factor]
  } deriving (Show, Read, Eq)

type Factor = (Expr Double, [Int])

evalFaultTreeM :: FaultTreeM a -> (a, FaultTree)
evalFaultTreeM a = (\(x, s, _) -> (x, s)) $
                   runRWS fullAction undefined (FaultTree 0 [])
  where
    fullAction = mdo
      x <- local (const n) a
      n <- gets faultTreeVariables
      return x

newVariableM :: FaultTreeM Int
newVariableM = do
  var <- gets faultTreeVariables
  modify $ \fts -> fts { faultTreeVariables = succ (faultTreeVariables fts) }
  return var

addFactorM :: Factor -> FaultTreeM ()
addFactorM factor = modify $ \fts ->
  fts { faultTreeFactors = factor : faultTreeFactors fts }

faultTreeLambdaM :: Double -> FaultTreeM Int
faultTreeLambdaM lambda = do
  var <- newVariableM
  vars <- ask
  let expr = distributionLambda vars var lambda
  addFactorM (expr, [var])
  return var

distributionTwoM :: (Int -> Int -> Int -> Int -> Expr Double) ->
                    Int -> Int -> FaultTreeM Int
distributionTwoM distr x y = do
  var <- newVariableM
  vars <- ask
  let expr = distr vars var x y
  addFactorM (expr, [x, y, var])
  return var

faultTreeAndM :: Int -> Int -> FaultTreeM Int
faultTreeAndM = distributionTwoM distributionAnd

simpleFaultTreeM :: FaultTreeM Int
simpleFaultTreeM = do
  a <- faultTreeLambdaM 15.0
  b <- faultTreeLambdaM 35.0
  faultTreeAndM a b
  c <- faultTreeLambdaM 3.0
  d <- faultTreeAndM a c
  return c

tellFactors :: MonadWriter [String] m => [Factor] -> m ()
tellFactors factors = do
  tell ["\\section{Factors}", ""]
  forM_ factors $
    \(expr, _) -> tell ["\\begin{dmath*} " ++ texify expr ++ "\\end{dmath*}", ""]

faultTreeIntegrate :: FaultTree -> (Expr Double, [String])
faultTreeIntegrate (FaultTree vars factors) = runWriter $ go factors 0
  where
  go fs i = if i < vars - 1
            then do
              fs' <- factorsEliminateVariable i fs
              go fs' (i + 1)
            else
              return . fst . head $ fs

factorsEliminateVariable :: MonadWriter [String] m => Int -> [Factor] -> m [Factor]
factorsEliminateVariable var factors = do
  tellFactors factors
  tell ["\\section{Integration of $x_{", show (succ var), "}$.}", ""]
  let (varFactors, restFactors) = partition (elem var . snd) factors
      expr = ExprN (Term (Atom 1 S.empty S.empty Nothing) (map fst varFactors))
  tell ["\\begin{dmath*} " ++ "\\int\\limits_0^{+\\infty} "
        ++ texify expr ++ "\\textrm{dx}_{" ++ show (var + 1)
        ++ "} \\end{dmath*}"
       , ""]
  let newExpr = integrate expr var Zero Infinity
      newVars = delete var . foldl union [] . map snd $ varFactors
  tell ["\\begin{dmath*} " ++ texify newExpr ++ "\\end{dmath*}", ""]
  return $ ((newExpr, newVars) : restFactors)

main :: IO ()
main = putStr . unlines . snd . faultTreeIntegrate . snd . evalFaultTreeM $ simpleFaultTreeM
