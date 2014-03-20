module Sesyrel.Expression.RealInfinite (
  RealInfinite (..)
  ) where

import Data.Ratio
import GHC.Real (Ratio((:%)))

class Num a => RealInfinite a where
  plusInfinity :: a
  minusInfinity :: a
  minusInfinity = negate plusInfinity
  nan :: a
  nan = plusInfinity - plusInfinity

instance Integral a => RealInfinite (Ratio a) where
  plusInfinity = 1 :% 0
