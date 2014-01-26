module Elimination (findOrdering) where

import Data.List (delete, elemIndex)
import Data.Maybe (fromJust)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Graph = IntMap [Int]

findOrdering :: [Int] -> [[Int]] -> [Int]
findOrdering vs cliques = go vs (makeGraph cliques)
  where
    go [] g = []
    go vs g = let v = getNextVertex vs g
              in v : go (delete v vs) (removeVertex v g)

getNextVertex :: [Int] -> Graph -> Int
getNextVertex vs g = let costs = map (costFunctionMinFill g) vs
                     in (vs !!) . fromJust $ elemIndex (minimum costs) costs

addClique :: [Int] -> Graph -> Graph
addClique [] = id
addClique (v : vs) = foldr ((.) . addEdge v) id vs . addClique vs

addEdge :: Int -> Int -> Graph -> Graph
addEdge a b | a == b = id 
            | otherwise = IM.insertWith (\_ ns -> if b `elem` ns then ns else b : ns) a [b]
              . IM.insertWith (\_ ns -> if a `elem` ns then ns else a : ns) b [a]

removeEdge :: Int -> Int -> Graph -> Graph
removeEdge a b = IM.adjust (delete b) a
                 . IM.adjust (delete a) b

removeVertex :: Int -> Graph -> Graph
removeVertex v g = let ns = g IM.! v
                   in IM.delete v . foldr ((.) . removeEdge v) id ns $ g

makeGraph :: [[Int]] -> Graph
makeGraph cliques = foldr ((.) . addClique) id cliques IM.empty

costFunctionMinFill :: Graph -> Int -> Int
costFunctionMinFill g v =
  let neighs = g IM.! v
      n = length neighs
      edge n = map ((,) n) $ g IM.! n
      inClique ns (a, b) = elem a neighs && elem b neighs
      neighEdges2 = length . filter (inClique neighs)
                   . concatMap edge $ neighs
  in n * (n - 1) - neighEdges2
