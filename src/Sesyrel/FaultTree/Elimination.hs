module Sesyrel.FaultTree.Elimination (findOrdering, pretend, Algorithm(..)) where

import Sesyrel.FaultTree.Base (Variable)

import Data.Function (on)
import Data.Foldable
import Data.Maybe (fromMaybe)
import Data.List (partition)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as S

type Clique = Set Variable
type Graph = Map Variable (Set Variable)

data Algorithm = GraphMinFill | GraphMinNeighbors

pretend :: [Variable] -> [[Variable]] -> [[[Variable]]]
pretend vs = map (map S.toList) . pretend' vs . map S.fromList

pretend' :: [Variable] -> [Clique] -> [[Clique]]
pretend' [] cliques = [cliques]
pretend' (v : vs) cliques =
  let (c, rest) = escapeClique v cliques
  in cliques : pretend' vs (if null c then rest else c : rest)

escapeClique :: Variable -> [Clique] -> (Clique, [Clique])
escapeClique v cliques =
  let (yes, no) = partition (elem v) cliques
      c = S.delete v $ fold yes
  in (c, no)

findOrdering :: Maybe Algorithm -> [Variable] -> [[Variable]] -> [(Variable, Int)]
findOrdering alg vs cs = findOrdering' alg (S.fromList vs) $ map S.fromList cs

findOrdering' :: Maybe Algorithm -> Set Variable -> [Clique] -> [(Variable, Int)]
findOrdering' Nothing = findOrdering' (Just GraphMinNeighbors)
findOrdering' (Just GraphMinFill) = findGraphOrdering costFunctionMinFill
findOrdering' (Just GraphMinNeighbors) = findGraphOrdering costFunctionMinNeighbors

findGraphOrdering :: (Graph -> Variable -> Int) -> Set Variable -> [Clique] -> [(Variable, Int)]
findGraphOrdering costFunction vars cliques = go vars (makeGraph cliques)
  where
    go vs g | S.null vs = []
            | otherwise = let v = getNextVertex (costFunction g) vs
                              (g', sz) = removeVertex v g
                          in v `seq` sz `seq` ((v, sz) : go (S.delete v vs) g')

getNextVertex :: (Variable -> Int) -> Set Variable -> Variable
getNextVertex f vs = let costs = S.mapMonotonic (\v -> (v, f v)) vs
                     in fst $ minimumBy (compare `on` snd) costs

addClique :: Graph -> Clique -> Graph
addClique graph clique = foldl' (flip addEdge) graph edges
  where
    f = S.toList clique
    edges = [(v1, v2) | v1 <- f, v2 <- f, v1 /= v2]

addEdge :: (Variable, Variable) -> Graph -> Graph
addEdge (a, b) = M.insertWith S.union a (S.singleton b)

removeEdge :: (Variable, Variable) -> Graph -> Graph
removeEdge (a, b) = M.adjust (S.delete b) a

removeVertex :: Variable -> Graph -> (Graph, Int)
removeVertex a g = let ns = fromMaybe S.empty (M.lookup a g)
                       sz = length ns
                   in ((`addClique` ns) . M.delete a $ foldl' (\g' b -> removeEdge (b, a) $ removeEdge (a, b) g') g ns, sz)

makeGraph :: [Clique] -> Graph
makeGraph cliques = foldl' addClique M.empty cliques

costFunctionMinFill :: Graph -> Variable -> Int
costFunctionMinFill g v =
  let neighs = fromMaybe S.empty (M.lookup v g)
      edgeNum k = S.size $ S.difference neighs (g M.! k)
  in sum . map edgeNum . S.toList $ neighs

costFunctionMinNeighbors :: Graph -> Variable -> Int
costFunctionMinNeighbors g v = S.size . fromMaybe S.empty . M.lookup v $ g
