{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Sesyrel.Expression.Texify (Texifiable(..), texify, texifyDoubleE) where

import Sesyrel.Expression.Base

import Data.Monoid (mempty, (<>), mconcat)
import Control.Applicative ((<$>))

import Data.Ratio

import Data.Maybe (fromJust, catMaybes)
import Data.List (intersperse, elemIndex)
import qualified Data.MultiSet as MS (toOccurList)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM (map, toList)
import qualified Data.Foldable as F (all)

import qualified Data.Text as T (Text)
import qualified Data.Text.Lazy as T (toStrict)
import qualified Data.Text.Lazy.Builder as TB (Builder, toLazyText, fromString, singleton)
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

instance (Num a, Ord a, Texifiable a) => Texifiable (Expr a) where
  texify' expr = let terms = texifyTerm <$> toList expr
                     signs = fst <$> terms
                     signStrs = (if head signs == '+' then mempty else TB.singleton '-')
                                : [ TB.fromString $ ' ' : s : " " | s <- tail signs ]
                 in mconcat $ zipWith (<>) signStrs (snd <$> terms)

instance Texifiable a => Texifiable (Symbol a) where
  texify' (Variable i) = "x_{" <> texify' i <> "}"
  texify' (Constant x) = texify' x

instance Texifiable a => Texifiable (DiffSym a) where
  texify' (DiffSym x y) = texify' x <> " - " <> texify' y

texifyTerm :: (Num a, Ord a, Texifiable a) => Term a -> (Char, TB.Builder)
texifyTerm (Term a es) | isOne a && not (null es) = (fst (texifyAtom a), exprs)
                       | otherwise = (sign, atom <> delimiter <> exprs)
    where
      (sign, atom) = texifyAtom a
      isOne (Atom k ds us is e) = abs k == 1 && nullBundle ds && nullBundle us && nullBundle is && F.all (== 0) e
      delimiter = if null es then "" else " \\cdot "
      exprs = mconcat . intersperse " \\cdot " $ texifyAndParen <$> es
      texifyAndParen e@(ExprC _ _) = "\\big[ " <> texify' e <> " \\big]"
      texifyAndParen e@(ExprN _) = texify' e

texifyAtom :: (Num a, Ord a, Texifiable a) => Atom a -> (Char, TB.Builder)
texifyAtom (Atom k deltas units inds expnt)
  | nullBundle deltas
    && nullBundle units
    && nullBundle inds
    && F.all (== 0) expnt = (sign, texify' absK)
  | otherwise =
    (,) sign $
    (if absK == 1 then mempty else texify' absK)
      <> (mconcat . intersperse " " . map texifyDelta . toListBundle $ deltas)
      <> (mconcat . intersperse " " . map texifyUnit . MS.toOccurList . getUnitBundle $ units)
      <> (mconcat . intersperse " " . map texifyIndicator . toListBundle $ inds)
      <> texifyExponent (IM.map negate expnt)
        where
          absK = abs k
          sign = if signum k == 1 then '+' else '-'
          texifyDelta d = "\\delta(" <> texify' d <> ")"
          texifyUnit (u, n) | n == 1 = "\\theta(" <> texify' u <> ")"
                            | otherwise = "\\theta(" <> texify' u <> ")^{" <> texify' n <> "}"
          texifyIndicator i = "\\epsilon(" <> texify' i <> ")"
          texifyExponent e = let vf = texifyVarForm e
                             in if F.all (== 0) expnt then mempty else "e^{" <> vf <> "}"

texifyVarForm :: (Num a, Ord a, Texifiable a) => IntMap a -> TB.Builder
texifyVarForm m | null pairs = mempty
                | otherwise = makeFirstVar (head pairs) <> mconcat (map makeSecondVar (tail pairs))
  where
    makeFirstVar ('+', t) = t
    makeFirstVar (s, t) = TB.singleton s <> t
    makeSecondVar (s, t) = TB.singleton s <> t
    pairs = catMaybes . map texifyVar . IM.toList $ m
    texifyVar (n, v) | v == 0 = Nothing
                     | otherwise = Just (sign v, showNum v <> "x_{" <> texify' n <> "}")
    sign v = if v > 0 then '+' else '-'
    showNum x = let ax = abs x in if ax == 1 then mempty else texify' ax
