{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree (
    FaultTree(..)
  , FaultTreeMonad
  , evalFaultTreeMonad
  , compileDynamicFaultTree
  , lambdaM
  , andM, orM
  , priorityAndOrM
  , switchM
  ) where

import Sesyrel.Distribution
import Sesyrel.Expression

import Prelude hiding (Rational)

import Control.Monad.RWS

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type FaultTreeMonad k = RWS Int () (FaultTree k)
type Variable = Int

newtype FaultTree k = FaultTree { unFaultTree :: IntMap (FaultTreeNode k) }
                  deriving (Show, Eq)

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeAnd Variable Variable
                     | FaultTreeOr Variable Variable
                     | FaultTreePriorityAndOr Variable Variable Variable
                     | FaultTreeSwitch Variable Variable Variable
                     deriving (Show, Eq)

evalFaultTreeMonad :: FaultTreeMonad k a -> (a, FaultTree k)
evalFaultTreeMonad a = (\(x, s, _) -> (x, s)) $
                       runRWS fullAction undefined (FaultTree IM.empty)
  where
    fullAction = mdo
      x <- local (const n) a
      n <- gets $ IM.size . unFaultTree
      return x

compileDynamicFaultTree :: FaultTree Rational -> [Factor]
compileDynamicFaultTree (FaultTree m) = map reNode $ IM.toList m
  where
    reNode :: (Int, FaultTreeNode Rational) -> Factor
    reNode (x, FaultTreeLambda k) = (distributionLambda x k, [x])
    reNode (x, FaultTreeAnd a b) = (distributionAnd a b x, [a, b, x])
    reNode (x, FaultTreeOr a b) = (distributionOr a b x, [a, b, x])
    reNode (x, FaultTreePriorityAndOr a b c) = (distributionPriorityAndOr a b c x, [a, b, c, x])
    reNode (x, FaultTreeSwitch a b c) = (distributionSwitch a b c x, [a, b, c, x])

lambdaM :: k -> FaultTreeMonad k Variable
lambdaM = addNodeM . FaultTreeLambda

andM, orM :: Variable -> Variable -> FaultTreeMonad k Variable
andM a b = addNodeM $ FaultTreeAnd a b
orM a b = addNodeM $ FaultTreeOr a b

priorityAndOrM, switchM :: Variable -> Variable -> Variable -> FaultTreeMonad k Variable
priorityAndOrM a b c = addNodeM $ FaultTreePriorityAndOr a b c
switchM s a b = addNodeM $ FaultTreeSwitch s a b

nextVariableM :: FaultTreeMonad k Variable
nextVariableM = do
  vars <- ask
  var <- gets $ IM.size . unFaultTree
  return (vars - var - 1)

addNodeM :: FaultTreeNode k -> FaultTreeMonad k Variable
addNodeM node = do
  var <- nextVariableM
  modify $ \fts ->
    FaultTree (IM.insert var node $ unFaultTree fts)
  return var
