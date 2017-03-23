{-# LANGUAGE OverloadedStrings #-}
module Sesyrel.FaultTree.Static
       ( compileStaticFaultTree
       , StaticFactor(..)
       ) where

import qualified Data.Vector as V
import Data.List (sort, sortBy, elemIndex)
import Data.Monoid ((<>))
import Data.Function (on)
import qualified Data.Text.Lazy.Builder as TB (Builder, fromString)

import Sesyrel.FaultTree.Base
import Sesyrel.Texify (Texifiable(..), texify)

data StaticFactor k = StaticFactor {
    factorVariables :: [Variable]
  , factorData :: V.Vector k
  } deriving (Show, Ord, Eq)

instance Show k => Texifiable (StaticFactor k) where
  texify' (StaticFactor vars vector) = "variables " <> sToB vars <> ", data " <> sToB (V.toList vector)
    where
      sToB :: Show a => a -> TB.Builder
      sToB = TB.fromString . show

instance (Show k, Fractional k) => Factor (StaticFactor k) where
  variables = factorVariables
  eliminate v f@(StaticFactor vs a) = maybe f eliminate' (elemIndex v vs)
    where
      eliminate' i = StaticFactor (var i) (arr i)
      var i = let (l, u) = splitAt i vs in l ++ tail u
      arr i = V.concat . halfList (V.zipWith (+)) $ cutInSlices a (2 ^ i)
  times = times'
  one = StaticFactor [] (V.singleton 1.0)
  texifyVariableElimination var factor = "eliminating " <> texify var <> " in " <> texify factor

generateStaticFactor :: [Variable] -> ([Bool] -> k) -> StaticFactor k
generateStaticFactor vars gen = StaticFactor (sort vars) (V.generate (2 ^ n) gen')
  where
    n = length vars
    gen' = gen . applyPermutation invSortOrder . ind2sub n
    sortOrder = sortingByPermutation compare vars
    invSortOrder = inversePermutation sortOrder

sortingByPermutation :: (a -> a -> Ordering) -> [a] -> [Int]
sortingByPermutation p = map fst . sortBy (p `on` snd) . zip [0..]

inversePermutation :: [Int] -> [Int]
inversePermutation = sortingByPermutation compare

applyPermutation :: [Int] -> [a] -> [a]
applyPermutation pmt xs = map (xs !!) pmt

times' :: Num k => StaticFactor k -> StaticFactor k -> StaticFactor k
times' (StaticFactor vs1 a1) (StaticFactor vs2 a2) = StaticFactor vs $ V.zipWith (*) a1' a2'
  where
    a1' = expandArray a1 (calcExpands vs1 vs 0)
    a2' = expandArray a2 (calcExpands vs2 vs 0)
    vs = unionVariables vs1 vs2
    calcExpands (vIn : vsIn) (vOut : vsOut) n | vIn == vOut = calcExpands vsIn vsOut (n + 1)
                                              | vIn > vOut = n : calcExpands (vIn : vsIn) vsOut (n + 1)
                                              | otherwise = error "calcExpands: somethng went wrong"
    calcExpands [] (_ : vsOut) n = n : calcExpands [] vsOut (n + 1)
    calcExpands [] [] _ = []
    calcExpands (_ : _) [] _ = error "calcExpands: something really went wrong"

expandArray :: V.Vector k -> [Int] -> V.Vector k
expandArray = foldl expandArrayBy1

expandArrayBy1 :: V.Vector k -> Int -> V.Vector k
expandArrayBy1 vec n = V.concat . doubleList $ cutInSlices vec $ 2 ^ n

doubleList :: [a] -> [a]
doubleList (v : vs) = v : v : doubleList vs
doubleList [] = []

halfList :: (a -> a -> b) -> [a] -> [b]
halfList f (v1 : v2 : vs) = f v1 v2 : halfList f vs
halfList _ [] = []
halfList _ [_] = error "halfList: odd list"

cutInSlices :: V.Vector k -> Int -> [V.Vector k]
cutInSlices v n | V.null v = []
                | otherwise = let (tv, dv) = V.splitAt n v
                              in tv : cutInSlices dv n


ind2sub :: Int -> Int -> [Bool]
ind2sub n = take n . go
  where
    go i = let (p, q) = i `divMod` 2
           in (q /= 0) : go p

compileStaticFaultTree :: Floating k => FaultTree k -> k -> [StaticFactor k]
compileStaticFaultTree ft t = map (uncurry $ compileNode) $ unFaultTree ft
  where
    --compileNode :: Floating k => Variable -> FaultTreeNode k -> StaticFactor k
    compileNode x (FaultTreeLambda l) =
      let p = exp (-l * t) in StaticFactor [x] (V.fromList [p, 1 - p])
    compileNode x (FaultTreeOr a b) = generateStaticFactor [a, b, x] $
                                        \[ba, bb, bx] -> if (ba || bb) == bx then 1.0 else 0.0
    compileNode x (FaultTreeAnd a b) = generateStaticFactor [a, b, x] $
                                         \[ba, bb, bx] -> if (ba && bb) == bx then 1.0 else 0.0
    compileNode _ _ = error "compileFaultTreeStatic: this FaultTree is not static"
