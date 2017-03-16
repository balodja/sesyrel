module Main where

import Test.QuickCheck (Arbitrary(..), choose, elements, once, sized)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework (Test, testGroup, defaultMain)

import Control.Applicative ((<$>))
import Control.Monad (join, foldM)
import Control.Monad.Writer (runWriter)
import Prelude hiding (Rational, product)
import Data.Either (partitionEithers)
import Data.List (delete, permutations)

import Sesyrel.Expression
import Sesyrel.FaultTree
import Sesyrel.Distribution (Factor, factorsEliminate)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.IntMap as IM (empty)

data DistrDef = DistrLambda Integer
              | DistrAnd Char Char
              | DistrOr Char Char
              | DistrPAndOr Char Char Char
              deriving (Show, Eq)

newtype TreeDef = TreeDef (Map Char DistrDef)
                  deriving (Show, Eq)

instance Arbitrary TreeDef where
  arbitrary = sized $ \n -> do
    numDepVars <- choose (7, 7 + n `div` 20)
    numBaseVars <- choose (4, 4 + n `div` 20)
    let makeBase c = do
          l <- choose (1, 10)
          return (c, DistrLambda l)
        makeBi' f t c = do
          let ks = M.keys t
          v1 <- elements ks
          v2 <- elements ks
          return $ M.insert c (f v1 v2) t
        makePAnd t c = do
          let ks = M.keys t
          v1 <- elements ks
          v2 <- elements ks
          v3 <- elements ks
          return $ M.insert c (DistrPAndOr v1 v2 v3) t
        makeBi t c = join . elements $ replicate 15 (makeBi' DistrAnd t c) ++ replicate 15 (makeBi' DistrOr t c) ++ replicate 1 (makePAnd t c)
    let baseVars = [toEnum (fromEnum 'a' + i) | i <- [0 .. numBaseVars - 1]]
        depVars = [toEnum (fromEnum 'a' + i) | i <- [numBaseVars .. numBaseVars + numDepVars - 1]]
    baseMap <- M.fromList <$> sequence (map makeBase baseVars)
    fullMap <- foldM makeBi baseMap depVars
    return $ TreeDef fullMap

  shrink (TreeDef def) =
    let labelVar (c, DistrLambda _) = Left c
        labelVar (c, DistrAnd a b) = Right (c, [a, b])
        labelVar (c, DistrOr a b) = Right (c, [a, b])
        labelVar (c, DistrPAndOr a b d) = Right (c, [a, b, d])
        (lambdaVars, distrVars) = partitionEithers (map labelVar (M.toList def))
        substDistr _ _ d@(DistrLambda _) = [d]
        substDistr v vs (DistrAnd a1 a2) = do
          b1 <- if a1 == v then vs else [a1]
          b2 <- if a2 == v then vs else [a2]
          return $ DistrAnd b1 b2
        substDistr v vs (DistrOr a1 a2) = do
          b1 <- if a1 == v then vs else [a1]
          b2 <- if a2 == v then vs else [a2]
          return $ DistrOr b1 b2
        substDistr v vs (DistrPAndOr a1 a2 a3) = do
          b1 <- if a1 == v then vs else [a1]
          b2 <- if a2 == v then vs else [a2]
          b3 <- if a3 == v then vs else [a3]
          return $ DistrPAndOr b1 b2 b3
        substVar v vs (c, d) | c == v = []
                             | otherwise = [(c, p) | p <- substDistr v vs d]
        go v vs = sequence . map (substVar v vs) . filter (\(c, _) -> c /= v)
    in do
      (v, vs) <- [(v, delete v lambdaVars) | v <- lambdaVars] ++ distrVars
      sh <- go v vs (M.toList def)
      return (TreeDef . M.fromList $ sh)

makeFaultTree :: TreeDef -> FaultTreeSesyrel
makeFaultTree (TreeDef def) = snd . evalFaultTreeSesyrelM $ treeM
  where
    treeM = foldM addToTree M.empty (M.toList def)
    addToTree :: Map Char Int -> (Char, DistrDef) -> FaultTreeSesyrelM (Map Char Int)
    addToTree assoc (c, DistrLambda l) = lambdaM (fromInteger l) >>= \i -> return $ M.insert c i assoc
    addToTree assoc (c, DistrAnd v1 v2) = andM (assoc M.! v1) (assoc M.! v2) >>= \i -> return $ M.insert c i assoc
    addToTree assoc (c, DistrOr v1 v2) = orM (assoc M.! v1) (assoc M.! v2) >>= \i -> return $ M.insert c i assoc
    addToTree assoc (c, DistrPAndOr v1 v2 v3) = priorityAndOrM (assoc M.! v1) (assoc M.! v2) (assoc M.! v3) >>= \i -> return $ M.insert c i assoc

checkFactors :: [Factor] -> [Int] -> Bool -> Bool
checkFactors factors xs opt = (== exprOne) . deepExpand . foldl product exprOne
                              . map fst . fst . runWriter
                              . factorsEliminate xs opt $ factors
  where
    exprOne = ExprN (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) [])

prop_completeness :: Bool -> TreeDef -> Bool
prop_completeness full def = all checkTree orders
  where
    FaultTreeSesyrel num factors = makeFaultTree def
    checkTree xs = checkFactors factors xs (not full)
    orders = if full then permutations [0 .. num - 1] else [[0 .. num - 1]]

tree1 :: TreeDef
tree1 =
  TreeDef (M.fromList
           [ ('b', DistrLambda 1)
           , ('d', DistrOr 'b' 'b')
           , ('f', DistrAnd 'b' 'b')
           , ('g', DistrAnd 'f' 'b')
           , ('k', DistrAnd 'g' 'f')
           , ('n', DistrOr 'k' 'b')
           , ('v', DistrAnd 'd' 'k')])

tree2 :: TreeDef
tree2 =
  TreeDef (M.fromList
           [ ('b', DistrLambda 1)
           , ('g', DistrAnd 'b' 'b')
           , ('k', DistrAnd 'g' 'b')
           , ('n', DistrOr 'k' 'b')])

tree3 :: TreeDef
tree3 =
  TreeDef (M.fromList
           [ ('a', DistrLambda 15)
           , ('b', DistrLambda 35)
           , ('c', DistrAnd 'a' 'b')
           , ('d', DistrLambda 3)
           , ('e', DistrAnd 'a' 'd')])

tree4 :: TreeDef
tree4 =
  TreeDef (M.fromList
           [ ('a', DistrLambda 10)
           , ('b', DistrLambda 3)
           , ('c', DistrPAndOr 'a' 'b' 'b')])

tree5 :: TreeDef
tree5 =
  TreeDef (M.fromList
           [ ('a', DistrLambda 10)
           , ('b', DistrAnd 'a' 'a')
           , ('c', DistrAnd 'a' 'b')
           , ('d', DistrOr 'a' 'c')
           , ('t', DistrPAndOr 'd' 'a' 'c')])

tree6 :: TreeDef
tree6 =
  TreeDef (M.fromList
           [ ('a', DistrLambda 70)
           , ('b', DistrLambda 70)
           , ('c', DistrLambda 10)
           , ('d', DistrPAndOr 'c' 'a' 'b')
           , ('e', DistrPAndOr 'c' 'a' 'b')
           , ('t', DistrOr 'd' 'e')])

tests_completeness :: Test
tests_completeness =
  testGroup "Complete integral over distributions should be equal to one"
  [ testProperty "large random distributions" (prop_completeness False)
  , testProperty "predefined distribution #1 in all orders"
    (once $ prop_completeness True tree1)
  , testProperty "predefined distribution #2 in all orders"
    (once $ prop_completeness True tree2)
  , testProperty "predefined distribution #3 in all orders"
    (once $ prop_completeness True tree3)
  , testProperty "predefined distribution #4 in all orders"
    (once $ prop_completeness True tree4)
  , testProperty "predefined distribution #5 in all orders"
    (once $ prop_completeness True tree5)
  , testProperty "predefined distribution #6 in all orders"
    (once $ prop_completeness True tree6)
  ]

main :: IO ()
main = defaultMain [ tests_completeness ]