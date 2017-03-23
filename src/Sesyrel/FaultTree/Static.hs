module Sesyrel.FaultTree.Static
       ( compileFaultTreeStatic
       , evalFaultTreeStatic
       ) where

import qualified Data.Vector as V
import Data.List (sort, sortBy, elemIndex, delete, union, partition)
import Data.Function (on)
import Data.Foldable (foldl')

import Sesyrel.FaultTree.Base
import Sesyrel.Elimination (findOrdering)

-- The following code is a real shame.

data Factor k = Factor {
    factorVariables :: [Int]
  , factorData :: V.Vector k
  } deriving (Show, Ord, Eq)

generateFactor :: [Int] -> ([Bool] -> k) -> Factor k
generateFactor vars gen = Factor (sort vars) (V.generate (2 ^ n) gen')
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

productFactors :: Fractional k => [Factor k] -> Factor k
productFactors = foldl' times (Factor [] (V.singleton 1.0))

times :: Num k => Factor k -> Factor k -> Factor k
times (Factor vs1 a1) (Factor vs2 a2) = Factor vs $ V.zipWith (*) a1' a2'
  where
    a1' = expandArray a1 (calcExpands vs1 vs 0)
    a2' = expandArray a2 (calcExpands vs2 vs 0)
    vs = unionVars vs1 vs2
    calcExpands (vIn : vsIn) (vOut : vsOut) n | vIn == vOut = calcExpands vsIn vsOut (n + 1)
                                              | vIn > vOut = n : calcExpands (vIn : vsIn) vsOut (n + 1)
                                              | otherwise = error "calcExpands: somethng went wrong"
    calcExpands [] (_ : vsOut) n = n : calcExpands [] vsOut (n + 1)
    calcExpands [] [] _ = []
    calcExpands (_ : _) [] _ = error "calcExpands: something really went wrong"

unionVars :: [Int] -> [Int] -> [Int]
unionVars (u : us) (v : vs) | u == v = v : unionVars us vs
                            | u < v = u : unionVars us (v : vs)
                            | otherwise = v : unionVars (u : us) vs
unionVars [] vs = vs
unionVars us [] = us

expandArray :: V.Vector k -> [Int] -> V.Vector k
expandArray = foldl expandArrayBy1

expandArrayBy1 :: V.Vector k -> Int -> V.Vector k
expandArrayBy1 vec n = V.concat . doubleList $ cutInSlices vec $ 2 ^ n

doubleList :: [a] -> [a]
doubleList (v : vs) = v : v : doubleList vs
doubleList [] = []

undoubleList :: (a -> a -> b) -> [a] -> [b]
undoubleList f (v1 : v2 : vs) = f v1 v2 : undoubleList f vs
undoubleList _ [] = []
undoubleList _ [_] = error "undoubleList: odd list"

cutInSlices :: V.Vector k -> Int -> [V.Vector k]
cutInSlices v n | V.null v = []
                | otherwise = let (tv, dv) = V.splitAt n v
                              in tv : cutInSlices dv n

eliminate :: Num k => Int -> Factor k -> Factor k
eliminate v f@(Factor vs a) = maybe f eliminate' (elemIndex v vs)
  where
    eliminate' i = Factor (var i) (arr i)
    var i = let (l, u) = splitAt i vs in l ++ tail u
    arr i = V.concat . undoubleList (V.zipWith (+)) $ cutInSlices a (2 ^ i)

ind2sub :: Int -> Int -> [Bool]
ind2sub n = take n . go
  where
    go i = let (p, q) = i `divMod` 2
           in (q /= 0) : go p

compileFaultTreeStatic :: Floating k => FaultTree k -> k -> [Factor k]
compileFaultTreeStatic ft t = map (uncurry $ compileNode t) $ unFaultTree ft
  where
    compileNode :: Floating k => k -> Int -> FaultTreeNode k -> Factor k
    compileNode t x (FaultTreeLambda l) =
      let p = exp (-l * t) in Factor [x] (V.fromList [p, 1 - p])
    compileNode _ x (FaultTreeOr a b) = generateFactor [a, b, x] $
                                        \[ba, bb, bx] -> if (ba || bb) == bx then 1.0 else 0.0
    compileNode _ x (FaultTreeAnd a b) = generateFactor [a, b, x] $
                                         \[ba, bb, bx] -> if (ba && bb) == bx then 1.0 else 0.0
    compileNode _ _ _ = error "compileFaultTreeStatic: this FaultTree is not static"

evalFaultTreeStatic :: Floating k => FaultTree k -> Int -> k -> V.Vector k
evalFaultTreeStatic ftree var t = vec
  where
    factors = compileFaultTreeStatic ftree t
    vars = map factorVariables factors
    varsForElimination = delete var $ foldl' union [] vars
    order = findOrdering Nothing varsForElimination vars
    Factor _ vec = productFactors $ foldl' eliminateInFactors factors order

eliminateInFactors :: Fractional k => [Factor k] -> Int -> [Factor k]
eliminateInFactors factors var = squeezed : untouched
  where
    (touched, untouched) = partition (\ (Factor vars _) -> var `elem` vars) factors
    squeezed = eliminate var $ productFactors touched
