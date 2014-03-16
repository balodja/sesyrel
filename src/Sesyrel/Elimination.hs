module Sesyrel.Elimination (findOrdering) where

import Data.List (delete, elemIndex)
import Data.Maybe (fromJust, fromMaybe)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Graph = IntMap [Int]

findOrdering :: [Int] -> [[Int]] -> [Int]
findOrdering vars cliques = go vars (makeGraph cliques)
  where
    go [] _ = []
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
removeVertex v g = let ns = fromMaybe [] (IM.lookup v g)
                   in IM.delete v . foldr ((.) . removeEdge v) id ns $ g

makeGraph :: [[Int]] -> Graph
makeGraph cliques = foldr ((.) . addClique) id cliques IM.empty

costFunctionMinFill :: Graph -> Int -> Int
costFunctionMinFill g v =
  let neighs = fromMaybe [] (IM.lookup v g)
      n = length neighs
      edge k = map ((,) k) $ g IM.! k
      inClique (a, b) = elem a neighs && elem b neighs
      neighEdges2 = length . filter inClique . concatMap edge $ neighs
  in n * (n - 1) - neighEdges2
