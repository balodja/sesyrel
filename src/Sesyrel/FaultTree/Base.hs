{-# LANGUAGE RecursiveDo #-}

module Sesyrel.FaultTree.Base (
    FaultTree(..)
  , FaultTreeMonad
  , Variable(..)
  , evalFaultTreeMonad
  , FaultTreeNode(..)
  , isDynamic
  , unionVariables
  , Factor(..)
  , productFactors
  , lambdaM
  , andM, orM
  , priorityAndOrM
  , switchM
  ) where

import Sesyrel.Texify (Texifiable(..))

import Prelude hiding (Rational)

import Control.Monad.RWS
import Data.Foldable (foldl')
import Data.Text (Text)

type FaultTreeMonad k = RWS Int () (FaultTree k)

newtype Variable = Variable { unVariable :: Int }
                 deriving (Show, Ord, Eq)

instance Texifiable Variable where
  texify' (Variable i) = texify' i

newtype FaultTree k = FaultTree { unFaultTree :: [(Variable, FaultTreeNode k)] }
                  deriving (Show, Eq)

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeAnd Variable Variable
                     | FaultTreeOr Variable Variable
                     | FaultTreePriorityAndOr Variable Variable Variable
                     | FaultTreeSwitch Variable Variable Variable
                     deriving (Show, Eq)

isDynamic :: FaultTree k -> Bool
isDynamic (FaultTree vs) = any isDynamic' $ map snd vs
  where
    isDynamic' (FaultTreeLambda _) = False
    isDynamic' (FaultTreeAnd _ _) = False
    isDynamic' (FaultTreeOr _ _) = False
    isDynamic' (FaultTreePriorityAndOr _ _ _) = True
    isDynamic' (FaultTreeSwitch _ _ _) = True

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

unionVariables :: [Variable] -> [Variable] -> [Variable]
unionVariables (u : us) (v : vs) | u == v = v : unionVariables us vs
                            | u < v = u : unionVariables us (v : vs)
                            | otherwise = v : unionVariables (u : us) vs
unionVariables [] vs = vs
unionVariables us [] = us

class Texifiable f => Factor f where
  variables :: f -> [Variable]
  eliminate :: Variable -> f -> f
  times :: f -> f -> f
  one :: f
  texifyVariableElimination :: Variable -> f -> Text

productFactors :: Factor f => [f] -> f
productFactors fs = foldl' times one fs

