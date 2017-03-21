module Sesyrel.FaultTree.Static
       ( ) where

import qualified Data.Vector as V

-- The following code is a real shame.

data Factor k = Factor (V.Vector Int) (Array k)

createFactor :: [Int] -> [k] -> Factor k
createFactor = undefined

times :: Factor k -> Factor k -> Factor k
times = undefined

eliminate :: Int -> Factor k
eliminate = undefined

data Array k = Array {
    arraySize :: V.Vector Int
  , arrayData :: V.Vector k
  } deriving (Show, Eq, Ord)

size :: Array k -> V.Vector Int
size = arraySize

toVector :: Array k -> V.Vector k
toVector = arrayData

fromVector :: V.Vector k -> Array k
fromVector v = Array (V.singleton $ V.length v) v

numel :: Array k -> Int
numel (Array sz _) = V.product sz

ind2sub :: V.Vector Int -> Int -> V.Vector Int
ind2sub sz i = V.map snd $ V.postscanl' go (i, 0) sz
  where
    go (ind, _) sz = ind `divMod` sz

sub2ind :: V.Vector Int -> V.Vector Int -> Int
sub2ind sz v = V.foldr' (\(s, i) x -> i + s * x) 0 $ V.zip sz v



compileFaultTreeStatic :: ()
compileFaultTreeStatic = ()
