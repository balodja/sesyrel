{-# LANGUAGE OverloadedStrings #-}

module Sesyrel.Texify (Texifiable(..), texify, texifyDoubleE) where

import Data.Ratio

import Data.List (intersperse, elemIndex)
import Data.Maybe (fromJust)
import Data.Monoid ((<>))

import qualified Data.Text as T (Text)
import qualified Data.Text.Lazy as T (toStrict)
import qualified Data.Text.Lazy.Builder as TB (Builder, toLazyText, fromString)
import qualified Data.Text.Lazy.Builder.Int as TB (decimal)
import qualified Data.Text.Lazy.Builder.RealFloat as TB (realFloat)


import Text.Printf (printf)

texify :: Texifiable a => a -> T.Text
texify = T.toStrict . TB.toLazyText . texify'

class Texifiable a where
  texify' :: a -> TB.Builder

instance Texifiable Integer where
  texify' = TB.decimal

instance Texifiable Int where
  texify' = TB.decimal

instance Texifiable Double where
  texify' = TB.realFloat

instance Texifiable a => Texifiable [a] where
  texify' l = "[" <> (mconcat . intersperse ", " . map texify' $ l) <> "]"

texifyDoubleE :: Int -> Double -> T.Text
texifyDoubleE n x = T.toStrict . TB.toLazyText $ texifyDoubleE' n x

texifyDoubleE' :: Int -> Double -> TB.Builder
texifyDoubleE' n x = let (l, r) = elemSplit 'e' (printf ("%." ++ show n ++ "e") x)
                         elemSplit y ys = splitAt (fromJust $ elemIndex y ys) ys
                     in TB.fromString $ if r == "e0" then l else l ++ " \\cdot 10^{" ++ tail r ++ "}"

instance (Integral a, Texifiable a) => Texifiable (Ratio a) where
  texify' z = let y = denominator z
                  x = numerator z
                  infty f | f > 0 = "+\\infty"
                          | f < 0 = "-\\infty"
                          | otherwise = "\\bot"
                  check 1 = texify' x
                  check 0 = infty x
                  check yy = "\\frac{" <> texify' x <> "}{" <> texify' yy <> "}"
              in check y
