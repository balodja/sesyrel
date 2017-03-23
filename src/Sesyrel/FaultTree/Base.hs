{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree.Base (
    FaultTree(..)
  , FaultTreeMonad
  , Variable(..)
  , evalFaultTreeMonad
  , FaultTreeNode(..)
  , Factor(..)
  , lambdaM
  , andM, orM
  , priorityAndOrM
  , switchM
  ) where

import Prelude hiding (Rational)

import Control.Monad.RWS

type FaultTreeMonad k = RWS Int () (FaultTree k)

newtype Variable = Variable { unVariable :: Int }
                 deriving (Show, Ord, Eq)

newtype FaultTree k = FaultTree { unFaultTree :: [(Variable, FaultTreeNode k)] }
                  deriving (Show, Eq)

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeAnd Variable Variable
                     | FaultTreeOr Variable Variable
                     | FaultTreePriorityAndOr Variable Variable Variable
                     | FaultTreeSwitch Variable Variable Variable
                     deriving (Show, Eq)

evalFaultTreeMonad :: FaultTreeMonad k a -> (a, FaultTree k)
evalFaultTreeMonad a = (\(x, s, _) -> (x, s)) $
                       runRWS fullAction undefined (FaultTree [])
  where
    fullAction = mdo
      x <- local (const n) a
      n <- gets $ length . unFaultTree
      return x

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
  var <- gets $ length . unFaultTree
  return $ Variable (vars - var - 1)

addNodeM :: FaultTreeNode k -> FaultTreeMonad k Variable
addNodeM node = do
  var <- nextVariableM
  modify $ (FaultTree . ((var, node) :) . unFaultTree)
  return var

class Factor f where
  variables :: f -> [Variable]
  eliminate :: Variable -> f -> f
  times :: f -> f -> f
  one :: f

