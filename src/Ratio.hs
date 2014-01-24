module Ratio (Ratio, Rational, numerator, denominator, (%)) where

import Prelude hiding (Rational)
import qualified Data.Ratio as R (numerator, denominator, (%))

data Ratio a = !a :% !a

numerator, denominator :: Ratio a -> a
numerator (x :% _) = x
denominator (_ :% y) = y

type Rational = Ratio Integer

instance (Num a, Eq a, Show a) => Show (Ratio a) where
  show (0 :% 0) = "NaN"
  show (1 :% 0) = "+Infinity"
  show ((-1) :% 0) = "-Infinity"
  show (x :% y) = show x ++ " % " ++ show y

instance Integral a => Num (Ratio a) where
  (p1 :% 0) + (p2 :% 0) = (p1 + p2) % 0
  (p1 :% 0) + _ = p1 :% 0
  _ + (p2 :% 0) = p2 :% 0
  (p1 :% q1) + (p2 :% q2) = (p1 * q2 + q1 * p2) % (q1 * q2)
  (p1 :% 0) - (p2 :% 0) = (p1 - p2) % 0
  (p1 :% 0) - _ = p1 :% 0
  _ - (p2 :% 0) = p2 :% 0
  (p1 :% q1) - (p2 :% q2) = (p1 * q2 - q1 * p2) % (q1 * q2)
  (p1 :% q1) * (p2 :% q2) = (p1 * p2) % (q1 * q2)
  negate (p :% q) = (-p) :% q
  abs (p :% q) = (abs p) :% q
  signum (p :% q) = signum p :% 1
  fromInteger i = fromInteger i :% 1

instance Integral a => Fractional (Ratio a) where
  (p1 :% q1) / (p2 :% q2) = (p1 * q2) % (q1 * p2)
  recip (0 :% x) = signum x :% 0
  recip (p :% q) = (q * signum p) :% (abs p)
  fromRational r = fromInteger (R.numerator r) % fromInteger (R.denominator r)

instance (Num a, Eq a) => Eq (Ratio a) where
  (0 :% 0) == _ = False
  _ == (0 :% 0) = False
  (p1 :% q1) == (p2 :% q2) = (p1 == p2) && (q1 == q2)
  (0 :% 0) /= _ = True
  _ /= (0 :% 0) = True
  (p1 :% q1) /= (p2 :% q2) = (p1 /= p2) || (q1 /= q2)

instance (Num a, Ord a) => Ord (Ratio a) where
  compare (p1 :% q1) (p2 :% q2) = compare (p1 * q2) (q1 * p2)

instance Integral a => Real (Ratio a) where
  toRational (p :% q) = (toInteger p) R.% (toInteger q)

infixl 7 %
(%) :: Integral a => a -> a -> Ratio a
x % y = reduce (x :% y)

reduce :: Integral a => Ratio a -> Ratio a
reduce (x :% 0) = signum x :% 0
reduce (x :% y) = let q = gcd x y in (signum y * (x `div` q)) :% ((abs y `div` q))
