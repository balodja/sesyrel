module Main where

import Test.QuickCheck (Arbitrary(..), choose, elements)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework (Test, testGroup, defaultMain)

import Control.Applicative ((<$>))
import Control.Monad (join, foldM)
import Control.Monad.Writer (runWriter)
import Prelude hiding (Rational, product)
import Data.Either (partitionEithers)
import Data.List (delete)

import Sesyrel.Expression
import Sesyrel.FaultTree
import Sesyrel.Distribution (Factor, factorsMarginalize)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.IntMap as IM (empty)

data DistrDef = DistrLambda Integer
              | DistrAnd Char Char
              | DistrOr Char Char
              deriving (Show, Eq)

newtype TreeDef = TreeDef (Map Char DistrDef)
                  deriving (Show, Eq)

instance Arbitrary TreeDef where
  arbitrary = do
    numDepVars <- choose (10, 20)
    numBaseVars <- choose (2, 5)
    let makeBase c = do
          l <- choose (1, 10)
          return (c, DistrLambda l)
        makeBi' f t c = do
          let ks = M.keys t
          v1 <- elements ks
          v2 <- elements ks
          return $ M.insert c (f v1 v2) t
        makeBi t c = join $ elements [makeBi' DistrAnd t c, makeBi' DistrOr t c]
    let baseVars = [toEnum (fromEnum 'a' + i) | i <- [0 .. numBaseVars - 1]]
        depVars = [toEnum (fromEnum 'a' + i) | i <- [numBaseVars .. numBaseVars + numDepVars - 1]]
    baseMap <- M.fromList <$> sequence (map makeBase baseVars)
    fullMap <- foldM makeBi baseMap depVars
    return $ TreeDef fullMap

  shrink (TreeDef def) =
    let labelVar (c, DistrLambda _) = Left c
        labelVar (c, DistrAnd a b) = Right (c, [a, b])
        labelVar (c, DistrOr a b) = Right (c, [a, b])
        (lambdaVars, distrVars) = partitionEithers (map labelVar (M.toList def))
        substDistr v vs (DistrAnd a1 a2) = do
          b1 <- if a1 == v then vs else [a1]
          b2 <- if a2 == v then vs else [a2]
          return $ DistrAnd b1 b2
        substDistr v vs (DistrOr a1 a2) = do
          b1 <- if a1 == v then vs else [a1]
          b2 <- if a2 == v then vs else [a2]
          return $ DistrOr b1 b2
        substDistr v vs d@(DistrLambda _) = [d]
        substVar v vs (c, d) | c == v = []
                             | otherwise = [(c, p) | p <- substDistr v vs d]
        go v vs = sequence . map (substVar v vs) . filter (\(c, _) -> c /= v)
    in do
      (v, vs) <- [(v, delete v lambdaVars) | v <- lambdaVars] ++ distrVars
      sh <- go v vs (M.toList def)
      return (TreeDef . M.fromList $ sh)

makeFaultTree :: TreeDef -> FaultTree
makeFaultTree (TreeDef def) = snd . evalFaultTreeM $ treeM
  where
    treeM = foldM addToTree M.empty (M.toList def)
    addToTree :: Map Char Int -> (Char, DistrDef) -> FaultTreeM (Map Char Int)
    addToTree assoc (c, DistrLambda l) = lambdaM (fromInteger l) >>= \i -> return $ M.insert c i assoc
    addToTree assoc (c, DistrAnd v1 v2) = andM (assoc M.! v1) (assoc M.! v2) >>= \i -> return $ M.insert c i assoc
    addToTree assoc (c, DistrOr v1 v2) = orM (assoc M.! v1) (assoc M.! v2) >>= \i -> return $ M.insert c i assoc

prop_completeness :: TreeDef -> Bool
prop_completeness def = (== exprOne) . deepExpand . foldl1 product . map fst . fst . runWriter . factorsMarginalize [] $ factors
  where
    FaultTree num factors = makeFaultTree def
    exprOne = ExprN (Term (Atom 1 emptyBundle emptyBundle IM.empty) [])

tests_completeness :: Test
tests_completeness = testGroup "Complete integral over distributions should be equal to one"
                     [ testProperty "large random distributions" prop_completeness ]

main :: IO ()
main = defaultMain [ tests_completeness ]