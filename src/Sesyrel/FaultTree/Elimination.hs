module Sesyrel.FaultTree.Elimination (findOrdering, pretend, Algorithm(..)) where

import Sesyrel.FaultTree.Base (Variable)

import Data.List (partition, nub, sort, union, delete, elemIndex)
import Data.Maybe (fromJust, fromMaybe)

import Data.Map (Map)
import qualified Data.Map as M

type Graph = Map Variable [Variable]

data Algorithm = GraphMinFill | GraphMinNeighbors | MinCardinality

pretend :: [Variable] -> [[Variable]] -> [[[Variable]]]
pretend [] cliques = [filter (not . null) cliques]
pretend (v : vs) cliques =
  let cs = filter (not . null) cliques
      (c, rest) = escapeClique v cs
  in cs : pretend vs (c : rest)

escapeClique :: Variable -> [[Variable]] -> ([Variable], [[Variable]])
escapeClique v cliques =
  let (yes, no) = partition (elem v) cliques
      c = delete v . nub . sort . foldl union [] $ yes
  in (c, no)

findOrdering :: Maybe Algorithm -> [Variable] -> [[Variable]] -> [Variable]
findOrdering Nothing = findOrdering (Just MinCardinality)
findOrdering (Just GraphMinFill) = findGraphOrdering costFunctionMinFill
findOrdering (Just GraphMinNeighbors) = findGraphOrdering costFunctionMinNeighbors
findOrdering (Just MinCardinality) = findMinCardinalityOrdering

findMinCardinalityOrdering :: [Variable] -> [[Variable]] -> [Variable]
findMinCardinalityOrdering [] _ = []
findMinCardinalityOrdering vs cliques =
  let costs = map (\v' -> length . fst $ escapeClique v' cliques) vs
      v = (vs !!) . fromJust $ elemIndex (minimum costs) costs
      (c, rest) = escapeClique v cliques
  in v : findMinCardinalityOrdering (delete v vs) (c : rest)

findGraphOrdering :: (Graph -> Variable -> Int) -> [Variable] -> [[Variable]] -> [Variable]
findGraphOrdering costFunction vars cliques = go vars (makeGraph cliques)
  where
    go [] _ = []
    go vs g = let v = getNextVertex costFunction vs g
              in v : go (delete v vs) (removeVertex v g)

getNextVertex :: (Graph -> Variable -> Int) -> [Variable] -> Graph -> Variable
getNextVertex f vs g = let costs = map (f g) vs
                       in (vs !!) . fromJust $ elemIndex (minimum costs) costs

addClique :: [Variable] -> Graph -> Graph
addClique [] = id
addClique (v : vs) = foldr ((.) . addEdge v) id vs . addClique vs

addEdge :: Variable -> Variable -> Graph -> Graph
addEdge a b | a == b = id 
            | otherwise = M.insertWith (\_ ns -> if b `elem` ns then ns else b : ns) a [b]
              . M.insertWith (\_ ns -> if a `elem` ns then ns else a : ns) b [a]

removeEdge :: Variable -> Variable -> Graph -> Graph
removeEdge a b = M.adjust (delete b) a
                 . M.adjust (delete a) b

removeVertex :: Variable -> Graph -> Graph
removeVertex v g = let ns = fromMaybe [] (M.lookup v g)
                   in M.delete v . foldr ((.) . removeEdge v) id ns $ g

makeGraph :: [[Variable]] -> Graph
makeGraph cliques = foldr ((.) . addClique) id cliques M.empty

costFunctionMinFill :: Graph -> Variable -> Int
costFunctionMinFill g v =
  let neighs = fromMaybe [] (M.lookup v g)
      n = length neighs
      edge k = map ((,) k) $ g M.! k
      inClique (a, b) = elem a neighs && elem b neighs
      neighEdges2 = length . filter inClique . concatMap edge $ neighs
  in n * (n - 1) - neighEdges2

costFunctionMinNeighbors :: Graph -> Variable -> Int
costFunctionMinNeighbors g v = length . fromMaybe [] . M.lookup v $ g
