module Sesyrel.FaultTree.Static
       ( ) where

import qualified Data.Vector as V
import Data.List (sort, sortBy)
import Data.Function (on)

-- The following code is a real shame.

data Factor k = Factor (V.Vector Int) (V.Vector k)
              deriving (Show, Ord, Eq)

generateFactor :: [Int] -> ([Bool] -> k) -> Factor k
generateFactor vars gen = Factor (V.fromList $ sort vars) (V.generate (2 ^ n) gen')
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

times :: Factor k -> Factor k -> Factor k
times = undefined

expandFactor :: Factor k -> V.Vector Int -> Factor k
expandFactor = undefined

expandArray :: V.Vector k -> [Int] -> V.Vector k
expandArray = foldl expandArrayBy1

expandArrayBy1 :: V.Vector k -> Int -> V.Vector k
expandArrayBy1 vec n = V.concat . doubleSlice . goSlice $ vec
  where
    sliceN = 2 ^ n :: Int
    goSlice :: V.Vector k -> [V.Vector k]
    goSlice v | V.null v = []
              | otherwise = let (tv, dv) = V.splitAt sliceN v
                            in tv : goSlice dv
    doubleSlice :: [V.Vector k] -> [V.Vector k]
    doubleSlice (v : vs) = v : v : doubleSlice vs
    doubleSlice [] = []

eliminate :: Int -> Factor k
eliminate = undefined

ind2sub :: Int -> Int -> [Bool]
ind2sub n = take n . go
  where
    go i = let (p, q) = i `divMod` 2
           in (q /= 0) : go p

compileFaultTreeStatic :: ()
compileFaultTreeStatic = ()
