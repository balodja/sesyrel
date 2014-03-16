{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree (
    FaultTree(..)
  , FaultTreeM
  , evalFaultTreeM
  , newVariableM
  , addFactorM
  , lambdaM
  , andM, orM
  , priorityAndOrM
  ) where

import Sesyrel.Distribution
import Sesyrel.Expression

import Prelude hiding (Rational)

import Control.Monad.RWS

type FaultTreeM = RWS Int [String] FaultTree

data FaultTree = FaultTree {
    faultTreeVariables :: Int
  , faultTreeFactors :: [Factor]
  } deriving (Show, Eq)

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
  vars <- ask
  var <- gets faultTreeVariables
  modify $ \fts -> fts { faultTreeVariables = succ (faultTreeVariables fts) }
  return (vars - var - 1)

addFactorM :: Factor -> FaultTreeM ()
addFactorM factor = modify $ \fts ->
  fts { faultTreeFactors = factor : faultTreeFactors fts }

lambdaM :: Rational -> FaultTreeM Int
lambdaM lambda = do
  var <- newVariableM
  let expr = distributionLambda var lambda
  addFactorM (expr, [var])
  return var

distributionTwoM :: (Int -> Int -> Int -> Expr Rational) ->
                    Int -> Int -> FaultTreeM Int
distributionTwoM distr x y = do
  var <- newVariableM
  let expr = distr var x y
  addFactorM (expr, [x, y, var])
  return var

andM :: Int -> Int -> FaultTreeM Int
andM = distributionTwoM distributionAnd

priorityAndOrM :: Int -> Int -> Int -> FaultTreeM Int
priorityAndOrM a b c = do
  var <- newVariableM
  let expr = distributionPriorityAndOr var a b c
  addFactorM (expr, [a, b, c, var])
  return var

orM :: Int -> Int -> FaultTreeM Int
orM = distributionTwoM distributionOr

{-
cspM :: Rational -> Int -> FaultTreeM Int
cspM lambda a = do
  b <- newVariableM
  let expr = distributionCspLambda b lambda a
  addFactorM (expr, [a, b])
  return b
-}
