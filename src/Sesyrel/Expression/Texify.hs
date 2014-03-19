{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Texify (Texifiable(..)) where

import Sesyrel.Expression.Base

import Control.Applicative ((<$>))

import Sesyrel.Expression.Ratio (Ratio, numerator, denominator)

import Data.List (intercalate)
import qualified Data.SignedMultiset as SM (toList)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM (map, toList)
import qualified Data.Foldable as F (all)

class Texifiable a where
  texify :: a -> String

instance Texifiable Integer where
  texify = show

instance Texifiable Int where
  texify = show

instance Texifiable Double where
  texify = show

instance (Integral a, Texifiable a) => Texifiable (Ratio a) where
  texify z = let y = denominator z
                 x = numerator z
                 infty f | f > 0 = "+\\infty"
                         | f < 0 = "-\\infty"
                         | otherwise = "\\bot"
                 check 1 = texify x
                 check 0 = infty x
                 check yy = "\\frac{" ++ texify x ++ "}{" ++ texify yy ++ "}"
             in check y

instance (Num a, Ord a, Texifiable a) => Texifiable (Expr a) where
  texify expr = let terms = texifyTerm <$> toList expr
                    signs = fst <$> terms
                    signStrs = (if head signs == '+' then "" else "-")
                               : [ ' ' : s : " " | s <- tail signs ]
                in concat $ zipWith (++) signStrs (snd <$> terms)

instance Texifiable a => Texifiable (Symbol a) where
  texify (Variable i) = "x_{" ++ texify i ++ "}"
  texify (Constant x) = texify x

instance Texifiable a => Texifiable (DiffSym a) where
  texify (DiffSym x y) = texify x ++ " - " ++ texify y

texifyTerm :: (Num a, Ord a, Texifiable a) => Term a -> (Char, String)
texifyTerm (Term a es) | isOne a && not (null exprs) = (fst (texifyAtom a), exprs)
                       | otherwise = (sign, atom ++ delimiter ++ exprs)
    where
      (sign, atom) = texifyAtom a
      isOne (Atom k ds us is e) = abs k == 1 && nullBundle ds && nullBundle us && nullBundle is && F.all (== 0) e
      delimiter = if null atom || null exprs then "" else " \\cdot "
      exprs = intercalate " \\cdot " $ texifyAndParen <$> es
      texifyAndParen e@(ExprC _ _) = "\\big[ " ++ texify e ++ " \\big]"
      texifyAndParen e@(ExprN _) = texify e

texifyAtom :: (Num a, Ord a, Texifiable a) => Atom a -> (Char, String)
texifyAtom (Atom k deltas units inds expnt)
  | nullBundle deltas
    && nullBundle units
    && nullBundle inds
    && F.all (== 0) expnt = (sign, texify absK)
  | otherwise =
    (,) sign $
    (if absK == 1 then [] else texify absK)
      ++ (unwords . map texifyDelta . toListBundle $ deltas)
      ++ (unwords . map texifyUnit . SM.toList . getUnitBundle $ units)
      ++ (unwords . map texifyIndicator . toListBundle $ inds)
      ++ texifyExponent (IM.map negate expnt)
        where
          absK = abs k
          sign = if signum k == 1 then '+' else '-'
          texifyDelta d = "\\delta(" ++ texify d ++ ")"
          texifyUnit (u, n) | n == 1 = "\\theta(" ++ texify u ++ ")"
                            | otherwise = "\\theta(" ++ texify u ++ ")^{" ++ show n ++ "}"
          texifyIndicator i = "\\epsilon(" ++ texify i ++ ")"
          texifyExponent e = let vf = texifyVarForm e
                             in if null vf then [] else "e^{" ++ vf ++ "}"

texifyVarForm :: (Num a, Ord a, Texifiable a) => IntMap a -> String
texifyVarForm = cutPlus . concatMap texifyVar . IM.toList
  where
    texifyVar (n, v) | v == 0 = ""
                     | otherwise = sign v : (showNum v ++ "x_{" ++ show n ++ "}")
    sign v = if v > 0 then '+' else '-'
    showNum x = let ax = abs x in if ax == 1 then [] else texify ax
    cutPlus ('+' : s) = s
    cutPlus s = s
