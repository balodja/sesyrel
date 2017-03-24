{-# LANGUAGE FlexibleContexts #-}
module Main where

import Test.QuickCheck (Arbitrary(..), Gen, choose, elements, once, sized)
import System.Random (Random)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework (Test, testGroup, defaultMain)

import Control.Applicative ((<$>))
import Control.Monad (join, foldM, replicateM)
import Control.Monad.Trans (lift)
import Prelude hiding (product)
import Data.Either (partitionEithers)
import Data.List (delete, permutations)

import Sesyrel.Expression (isOneExpr)
import Sesyrel.FaultTree
import Sesyrel.FaultTree.Dynamic
import Sesyrel.FaultTree.Static

import qualified Data.Vector as V (length, (!))

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.IntMap as IM (empty)

{-
data DistrDef = DistrLambda Integer
              | DistrAnd Char Char
              | DistrOr Char Char
              | DistrPAndOr Char Char Char
              deriving (Show, Eq)

newtype TreeDef = TreeDef (Map Char DistrDef)
                  deriving (Show, Eq)
-}

data StaticFaultTree = StaticFaultTree Double (FaultTree Double)
                     deriving Show

newtype DynamicFaultTree = DynamicFaultTree (FaultTree Rational)
                           deriving Show

monadToDyn :: Monad m => FaultTreeMonadT Rational m a -> m DynamicFaultTree
monadToDyn act = (DynamicFaultTree . snd) <$> (runFaultTreeMonadT act)

monadToStat :: Monad m => FaultTreeMonadT Double m Double -> m StaticFaultTree
monadToStat act = (uncurry StaticFaultTree) <$> (runFaultTreeMonadT act)

pickBase :: Num k => (Integer, Integer) -> FaultTreeMonadT k Gen Variable
pickBase range = do
  l <- lift $ choose range
  addNodeM $ FaultTreeLambda (fromInteger l)

pickDependent :: (Int, Int, Int) -> FaultTreeMonadT k Gen Variable
pickDependent (nAnd, nOr, nPAnd) =
  let variants = replicate nAnd pickAnd ++ replicate nOr pickOr ++ replicate nPAnd pickPAnd
      pickVar = do {vars <- variablesM; lift $ elements vars}
      pickAnd = do {v1 <- pickVar; v2 <- pickVar; addNodeM $ FaultTreeAnd v1 v2}
      pickOr = do {v1 <- pickVar; v2 <- pickVar; addNodeM $ FaultTreeOr v1 v2}
      pickPAnd = do {v1 <- pickVar; v2 <- pickVar; v3 <- pickVar;
                     addNodeM $ FaultTreePriorityAndOr v1 v2 v3}
  in join . lift $ elements variants

variants :: (Variable, [Variable]) -> Variable -> [Variable]
variants (v, vs) a = if a == v then vs else [a]

substituteNode :: (Variable, [Variable]) -> FaultTreeNode k -> [FaultTreeNode k]
substituteNode _ l@(FaultTreeLambda _) = [l]
substituteNode v (FaultTreeAnd a1 a2) =
  [FaultTreeAnd v1 v2 | v1 <- variants v a1, v2 <- variants v a2]
substituteNode v (FaultTreeOr a1 a2) =
  [FaultTreeOr v1 v2 | v1 <- variants v a1, v2 <- variants v a2]
substituteNode v (FaultTreePriorityAndOr a1 a2 a3) =
  [FaultTreePriorityAndOr v1 v2 v3 | v1 <- variants v a1
                                   , v2 <- variants v a2
                                   , v3 <- variants v a3]

variablesNode :: FaultTreeNode k -> [Variable]
variablesNode (FaultTreeLambda _) = []
variablesNode (FaultTreeAnd a b) = [a, b]
variablesNode (FaultTreeOr a b) = [a, b]
variablesNode (FaultTreePriorityAndOr a b c) = [a, b, c]

fingers :: [a] -> [(a, [a])]
fingers = go id
  where
    go :: ([a] -> [a]) -> [a] -> [(a, [a])]
    go diff (x : xs) = (x, diff xs) : go (diff . (x :)) xs
    go diff [] = []

shrinkFaultTree :: FaultTree k -> [FaultTree k]
shrinkFaultTree (FaultTree pairs) =
    let substitutePair :: (Variable, [Variable])
                          -> (Variable, FaultTreeNode k)
                          -> [(Variable, FaultTreeNode k)]
        substitutePair v (var, node) =
          [(var, node') | node' <- substituteNode v node]
        substituteFinger :: ((Variable, FaultTreeNode k), [(Variable, FaultTreeNode k)])
                            -> [[(Variable, FaultTreeNode k)]]
        substituteFinger ((var, node), pairs) =
          sequence [substitutePair (var, variablesNode node) pair | pair <- pairs]
        --trees :: [[(Variable, FaultTreeNode k)]]
        trees = [tree | f <- fingers pairs, tree <- substituteFinger f]
    in map FaultTree trees

instance Arbitrary StaticFaultTree where
  arbitrary = sized $ \n -> monadToStat $ do
    numBaseVars <- lift $ choose (8, 8 + n `div` 5)
    baseVars <- replicateM numBaseVars $ pickBase (1, 10)
    numDepVars <- lift $ choose (12, 12 + n `div` 2)
    depVars <- replicateM numDepVars $ pickDependent (15, 15, 0)
    time <- lift $ choose (1, 10 :: Int)
    return (realToFrac time)

  shrink (StaticFaultTree t tree) = map (StaticFaultTree t) $ shrinkFaultTree tree

instance Arbitrary DynamicFaultTree where
  arbitrary = sized $ \n -> monadToDyn $ do
    numBaseVars <- lift $ choose (4, 4 + n `div` 20)
    baseVars <- replicateM numBaseVars $ pickBase (1, 10)
    numDepVars <- lift $ choose (7, 7 + n `div` 20)
    depVars <- replicateM numDepVars $ pickDependent (15, 15, 1)
    return ()

  shrink (DynamicFaultTree tree) = map DynamicFaultTree $ shrinkFaultTree tree


prop_dynamic_completeness :: Bool -> DynamicFaultTree -> Bool
prop_dynamic_completeness full (DynamicFaultTree ft) = all checkFactors orders
  where
    factors = compileDynamicFaultTree ft
    variables = faultTreeVariables ft
    checkFactors xs = isOneExpr . dynamicFactorExpr . productFactors $ factorsEliminate xs (not full) factors
    orders = if full then permutations variables else [variables]

prop_static_completeness :: Bool -> StaticFaultTree -> Bool
prop_static_completeness full (StaticFaultTree time ft) = all checkFactors orders
  where
    factors = compileStaticFaultTree ft time
    variables = faultTreeVariables ft
    checkFactors xs = checkOne . productFactors $ factorsEliminate xs (not full) factors
    checkOne (StaticFactor [] vec) = (V.length vec == 1) && ((vec V.! 0 - 1) < 1e-10)
    checkOne _ = error "prop_static_completeness: this should not happen"
    orders = if full then permutations variables else [variables]

tree1 :: Num k => FaultTree k
tree1 = snd . runFaultTreeMonad $ do
  b <- lambdaM 1
  d <- orM b b
  f <- andM b b
  g <- andM f b
  k <- andM g f
  n <- orM k b
  v <- andM d k
  return ()

tree2 :: Num k => FaultTree k
tree2 = snd . runFaultTreeMonad $ do
  b <- lambdaM 1
  g <- andM b b
  k <- andM g b
  n <- orM k b
  return ()

tree3 :: Num k => FaultTree k
tree3 = snd . runFaultTreeMonad $ do
  a <- lambdaM 15
  b <- lambdaM 35
  c <- andM a b
  d <- lambdaM 3
  e <- andM a d
  return ()

tree4 :: Num k => FaultTree k
tree4 = snd . runFaultTreeMonad $ do
  a <- lambdaM 10
  b <- lambdaM 3
  c <- priorityAndOrM a b b
  return ()

tree5 :: Num k => FaultTree k
tree5 = snd . runFaultTreeMonad $ do
  a <- lambdaM 10
  b <- andM a a
  c <- andM a b
  d <- orM a c
  t <- priorityAndOrM d a c
  return ()

tree6 :: Num k => FaultTree k
tree6 = snd . runFaultTreeMonad $ do
  a <- lambdaM 70
  b <- lambdaM 70
  c <- lambdaM 10
  d <- priorityAndOrM c a b
  e <- priorityAndOrM c a b
  t <- orM d e
  return ()

tests_dynamic_completeness :: Test
tests_dynamic_completeness =
  testGroup "Complete integral over distributions should be equal to one"
  [ testProperty "large random distributions" (prop_dynamic_completeness False)
  , testProperty "predefined distribution #1 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree1)
  , testProperty "predefined distribution #2 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree2)
  , testProperty "predefined distribution #3 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree3)
  , testProperty "predefined distribution #4 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree4)
  , testProperty "predefined distribution #5 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree5)
  , testProperty "predefined distribution #6 in all orders"
    (once $ prop_dynamic_completeness True $ DynamicFaultTree tree6)
  ]

tests_static_completeness :: Test
tests_static_completeness =
  testGroup "Complete elimination over discrete distributions should be equal to one"
  [ testProperty "large random distributions" (prop_static_completeness False)
  , testProperty "predefined distribution #1 in all orders"
    (once $ prop_static_completeness True $ StaticFaultTree 1.5 tree1)
  , testProperty "predefined distribution #2 in all orders"
    (once $ prop_static_completeness True $ StaticFaultTree 1.5 tree2)
  , testProperty "predefined distribution #3 in all orders"
    (once $ prop_static_completeness True $ StaticFaultTree 1.5 tree3)
  ]

main :: IO ()
main = defaultMain [ tests_static_completeness ]
