{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree (
    FaultTree(..)
  , FaultTreeMonad
  , evalFaultTreeMonad
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


newtype FaultTree k = FaultTree { unFaultTree :: IntMap (FaultTreeNode k) }
                  deriving (Show, Eq)

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeAnd Int Int
                     | FaultTreeOr Int Int
                     | FaultTreePriorityAndOr Int Int Int
                     | FaultTreeSwitch Int Int Int
                     deriving (Show, Eq)

evalFaultTreeMonad :: FaultTreeMonad k a -> (a, FaultTree k)
evalFaultTreeMonad a = (\(x, s, _) -> (x, s)) $
                       runRWS fullAction undefined (FaultTree IM.empty)
  where
    fullAction = mdo
      x <- local (const n) a
      n <- gets $ IM.size . unFaultTree
      return x

lambdaM :: k -> FaultTreeMonad k Int
lambdaM = addNodeM . FaultTreeLambda

andM, orM :: Int -> Int -> FaultTreeMonad k Int
andM a b = addNodeM $ FaultTreeAnd a b
orM a b = addNodeM $ FaultTreeOr a b

priorityAndOrM, switchM :: Int -> Int -> Int -> FaultTreeMonad k Int
priorityAndOrM a b c = addNodeM $ FaultTreePriorityAndOr a b c
switchM s a b = addNodeM $ FaultTreeSwitch s a b

nextVariableM :: FaultTreeMonad k Int
nextVariableM = do
  vars <- ask
  var <- gets $ IM.size . unFaultTree
  return (vars - var - 1)

addNodeM :: FaultTreeNode k -> FaultTreeMonad k Int
addNodeM node = do
  var <- nextVariableM
  modify $ \fts ->
    FaultTree (IM.insert var node $ unFaultTree fts)
  return var
