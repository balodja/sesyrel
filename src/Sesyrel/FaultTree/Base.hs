{-# LANGUAGE RecursiveDo, GeneralizedNewtypeDeriving #-}

module Sesyrel.FaultTree.Base (
    FaultTree(..)
  , unFaultTree
  , FaultTreeMonadT
  , FaultTreeMonad
  , Variable(..)
  , unVariable
  , runFaultTreeMonadT
  , runFaultTreeMonad
  , FaultTreeNode(..)
  , isDynamic
  , faultTreeVariables
  , unionVariables
  , Factor(..)
  , productFactors
  , variablesM
  , addNodeM
  , lambdaM, constantM
  , notM, andM, orM
  , voterM
  , priorityAndOrM
  , switchM
  ) where

import Sesyrel.Texify (Texifiable(..))

import Prelude hiding (Rational)

import Control.Monad.State
import Control.Monad.Identity
import Data.Foldable (foldl')
import Data.Text (Text)

type FaultTreeMonadT k m = StateT (FaultTree k) m

type FaultTreeMonad k = FaultTreeMonadT k Identity

newtype Variable = Variable Int
                 deriving (Show, Ord, Eq, Num, Enum)

unVariable :: Variable -> Int
unVariable (Variable i) = i

instance Texifiable Variable where
  texify' (Variable i) = texify' i

newtype FaultTree k = FaultTree [(Variable, FaultTreeNode k)]
                  deriving (Show, Eq)

unFaultTree :: FaultTree k -> [(Variable, FaultTreeNode k)]
unFaultTree (FaultTree ps) = ps

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeConstant k
                     | FaultTreeNot Variable
                     | FaultTreeAnd Variable Variable
                     | FaultTreeOr Variable Variable
                     | FaultTreePriorityAndOr Variable Variable Variable
                     | FaultTreeSwitch Variable Variable Variable
                     deriving (Show, Eq)

isDynamic :: FaultTree k -> Bool
isDynamic (FaultTree vs) = any isDynamic' $ map snd vs
  where
    isDynamic' (FaultTreeLambda _) = False
    isDynamic' (FaultTreeConstant _) = False
    isDynamic' (FaultTreeNot _) = False
    isDynamic' (FaultTreeAnd _ _) = False
    isDynamic' (FaultTreeOr _ _) = False
    isDynamic' (FaultTreePriorityAndOr _ _ _) = True
    isDynamic' (FaultTreeSwitch _ _ _) = True

runFaultTreeMonad :: FaultTreeMonad k a -> (a, FaultTree k)
runFaultTreeMonad = runIdentity . runFaultTreeMonadT

runFaultTreeMonadT :: Monad m => FaultTreeMonadT k m a -> m (a, FaultTree k)
runFaultTreeMonadT a = (\(x, FaultTree s) -> (x, FaultTree $ reverse s)) <$>
                       runStateT a (FaultTree [])

lambdaM, constantM :: Monad m => k -> FaultTreeMonadT k m Variable
lambdaM = addNodeM . FaultTreeLambda
constantM = addNodeM . FaultTreeConstant

notM :: Monad m => Variable -> FaultTreeMonadT k m Variable
notM = addNodeM . FaultTreeNot

andM, orM :: Monad m => Variable -> Variable -> FaultTreeMonadT k m Variable
andM a b = addNodeM $ FaultTreeAnd a b
orM a b = addNodeM $ FaultTreeOr a b

voterM :: (Num k, Monad m) => Int -> [Variable] -> FaultTreeMonadT k m Variable
voterM k vars = do
  initial <- replicateM k (constantM 0)
  let step voters v = do
        v0 <- constantM 1
        zipWithM (\u u' -> andM v u' >>= orM u) voters (v0 : voters)
  final <- foldM step initial vars
  return $ last final

priorityAndOrM, switchM :: Monad m => Variable -> Variable -> Variable -> FaultTreeMonadT k m Variable
priorityAndOrM a b c = addNodeM $ FaultTreePriorityAndOr a b c
switchM s a b = addNodeM $ FaultTreeSwitch s a b

addNodeM :: Monad m => FaultTreeNode k -> FaultTreeMonadT k m Variable
addNodeM node = state $ \(FaultTree nodes) ->
  let var = Variable $ length nodes
  in (var, FaultTree $ (var, node) : nodes)

variablesM :: Monad m => FaultTreeMonadT k m [Variable]
variablesM = do
  FaultTree nodes <- get
  return $ [0 .. (fromIntegral $ length nodes - 1)]

faultTreeVariables :: FaultTree k -> [Variable]
faultTreeVariables (FaultTree ps) = map fst ps

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
