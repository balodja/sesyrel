module Sesyrel.Elimination (findOrdering, pretend) where

import Data.List (partition, nub, sort, union, delete, elemIndex)
import Data.Maybe (fromJust, fromMaybe)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Graph = IntMap [Int]

data Algorithm = MinFill | MinNeighbors

pretend :: [Int] -> [[Int]] -> [[[Int]]]
pretend [] cliques = [filter (not . null) cliques]
pretend (v : vs) cliques =
  let cs = filter (not . null) cliques
      (yes, no) = partition (elem v) cs
      c = delete v . nub . sort . foldl union [] $ yes
  in cs : pretend vs (c : no)

findOrdering :: Maybe Algorithm -> [Int] -> [[Int]] -> [Int]
findOrdering Nothing vars cliques = findOrdering (Just MinFill) vars cliques
findOrdering (Just algo) vars cliques = go vars (makeGraph cliques)
  where
    costFunction = case algo of
      MinFill -> costFunctionMinFill
      MinNeighbors -> costFunctionMinNeighbors
    go [] _ = []
    go vs g = let v = getNextVertex costFunction vs g
              in v : go (delete v vs) (removeVertex v g)

getNextVertex :: (Graph -> Int -> Int) -> [Int] -> Graph -> Int
getNextVertex f vs g = let costs = map (f g) vs
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

costFunctionMinNeighbors :: Graph -> Int -> Int
costFunctionMinNeighbors g v = length . fromMaybe [] . IM.lookup v $ g