module Main where

import Test.QuickCheck (Arbitrary(..), choose, elements)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework (Test, testGroup, defaultMain)

import Control.Applicative ((<$>))
import Control.Monad (join, foldM)
import Control.Monad.Writer (runWriter)
import Prelude hiding (Rational, product)

import Sesyrel.Expression
import Sesyrel.FaultTree
import Sesyrel.Distribution (Factor, factorsMarginalize)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.IntMap as IM (empty)

data DistrDef = DistrLambda Rational
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
          return (c, DistrLambda (fromInteger l))
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

makeFaultTree :: TreeDef -> FaultTree
makeFaultTree (TreeDef def) = snd . evalFaultTreeM $ treeM
  where
    treeM = foldM addToTree M.empty (M.toList def)
    addToTree :: Map Char Int -> (Char, DistrDef) -> FaultTreeM (Map Char Int)
    addToTree assoc (c, DistrLambda l) = lambdaM l >>= \i -> return $ M.insert c i assoc
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