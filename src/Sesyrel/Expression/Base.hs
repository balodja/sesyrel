{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Base (
    Expr(..), Term(..) , Atom(..)
  , Symbol(..), DiffSym(..)
  , toList, fromList
  , normalizeDs, substitute, substituteAtom
  , expand, deepExpand
  , product, makeSingleU, makeSingleD
  , groupifyAtoms, cancelUsAtom
  ) where

import Control.Applicative ((<$>))

import Data.List (partition)
import Data.Either (partitionEithers)
import Sesyrel.Expression.Ratio (RealInfinite(..))

import Prelude hiding (product)
import qualified Prelude as Prelude (product)

import Data.Set (Set)
import qualified Data.Set as S
  (map, empty, union, singleton)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
  (empty, delete, insert, findWithDefault, unionWith)

data Expr a = ExprC (Term a) (Expr a)
            | ExprN (Term a)
            deriving (Show, Eq)

data Term a = Term {
    termAtom :: Atom a
  , termExpr :: [Expr a]
  } deriving (Show, Eq)

data Atom a = Atom {
    atomConstant :: a
  , atomDeltas :: Set (DiffSym a)
  , atomUnits :: [DiffSym a]
  , atomExponent :: IntMap a
  } deriving (Show, Eq)

data Symbol a = Variable !Int
              | Constant !a
              deriving (Show, Eq)

instance Ord a => Ord (Symbol a) where
  compare (Constant x) (Constant y) = compare x y
  compare (Constant _) (Variable _) = LT
  compare (Variable _) (Constant _) = GT
  compare (Variable i) (Variable j) = compare i j

data DiffSym a = DiffSym {
    diffSymFst :: !(Symbol a)
  , diffSymSnd :: !(Symbol a)
  } deriving (Show, Eq)

instance Ord a => Ord (DiffSym a) where
  compare (DiffSym x1 y1) (DiffSym x2 y2) =
    case compare x1 x2 of
      LT -> LT
      EQ -> compare y1 y2
      GT -> GT

specialExp :: (RealInfinite a, Eq a) => a -> a
specialExp x | x == 0 = 1 
             | x == plusInfinity = plusInfinity
             | x == minusInfinity = 0
             | otherwise = error "specialExp: non-cardinal exponent"

toList :: Expr a -> [Term a]
toList (ExprC t e) = t : toList e
toList (ExprN t) = [t]

fromList :: [Term a] -> Expr a
fromList (t : []) = ExprN t
fromList (t : ts) = ExprC t (fromList ts)
fromList [] = error "fromList: term list is empty"

mapExpr :: (Term a -> Term a) -> Expr a -> Expr a
mapExpr f = fromList . map f . toList

normalizeDs :: (Num a, Ord a) => Expr a -> Expr a
normalizeDs = mapExpr normalizeDsTerm

normalizeDsTerm :: (Num a, Ord a) => Term a -> Term a
normalizeDsTerm (Term a es) = Term (normalizeDsAtom a) (normalizeDs <$> es)

normalizeDsAtom :: (Num a, Ord a) => Atom a -> Atom a
normalizeDsAtom (Atom k ds us e) = Atom k (S.map swapDelta ds) us e
  where
    swapDelta d@(DiffSym (Variable ix) (Variable iy))
      | ix < iy = d
      | otherwise = DiffSym (Variable iy) (Variable ix)
    swapDelta d@(DiffSym c@(Constant _) i@(Variable _))
      = DiffSym i c
    swapDelta d = d

substitute :: (RealInfinite a, Ord a) => Int -> Symbol a -> Expr a -> Expr a
substitute v sym = mapExpr (substituteTerm v sym)

substituteTerm :: (RealInfinite a, Ord a) => Int -> Symbol a -> Term a -> Term a
substituteTerm v sym (Term a es) = Term (substituteAtom v sym a) (substitute v sym <$> es)

substituteAtom :: (RealInfinite a, Ord a) => Int -> Symbol a -> Atom a -> Atom a
substituteAtom v sym (Atom k1 ds us e1) = normalizeDsAtom $
  Atom (k1 * k2) (S.map (substituteDiffSym v sym) ds) (substituteDiffSym v sym <$> us) e2
  where
    (k2, e2) = substituteExp v sym e1

substituteDiffSym :: Int -> Symbol a -> DiffSym a -> DiffSym a
substituteDiffSym i s (DiffSym x y) = DiffSym (substituteSym i s x) (substituteSym i s y)

substituteSym :: Int -> Symbol a -> Symbol a -> Symbol a
substituteSym i s c@(Constant _) = c
substituteSym i s v@(Variable j) | i == j = s
                                 | otherwise = v

substituteExp :: (RealInfinite a, Eq a) => Int -> Symbol a -> IntMap a -> (a, IntMap a)
substituteExp i (Constant c) vec | value == 0 = (1, vec)
                                 | otherwise = (specialExp (-value * c), IM.delete i vec)
                                   where value = IM.findWithDefault 0 i vec
substituteExp i (Variable j) vec | vi == 0 = (1, vec)
                                 | otherwise = (1, IM.insert j (vi + vj) . IM.delete i $ vec)
                                   where vi = IM.findWithDefault 0 i vec
                                         vj = IM.findWithDefault 0 j vec              

deepExpand :: (Num a, Ord a) => Expr a -> Expr a
deepExpand e | isExpandable e = deepExpand (expand e)
             | otherwise = e
  where
    isExpandable = any isExpandableTerm . toList
    isExpandableTerm (Term _ []) = False
    isExpandableTerm _ = True

expand :: (Num a, Ord a) => Expr a -> Expr a
expand = fromList . concatMap (toList . expandTerm) . toList

expandTerm :: (Num a, Ord a) => Term a -> Expr a
expandTerm (Term a []) = ExprN $ Term a []
expandTerm (Term a es) =
  fromList . map (foldl productTerm (Term a [])) . sequence $ toList <$> es

product :: (Num a, Ord a) => Expr a -> Expr a -> Expr a
product e1 e2 = ExprN (Term (Atom 1 S.empty [] IM.empty) [e1, e2])

productTerm :: (Num a, Ord a) => Term a -> Term a -> Term a
productTerm (Term a1 e1) (Term a2 e2) = Term (productAtom a1 a2) (e1 ++ e2)

productAtom :: (Num a, Ord a) => Atom a -> Atom a -> Atom a
productAtom (Atom k1 d1 u1 e1) (Atom k2 d2 u2 e2) =
  Atom (k1 * k2) (d1 `S.union` d2) (u1 ++ u2) (IM.unionWith (+) e1 e2)

makeSingleD :: Int -> Int -> Set (DiffSym a)
makeSingleD a b = S.singleton (DiffSym (Variable a) (Variable b))

makeSingleU :: Int -> Int -> [DiffSym a]
makeSingleU a b = [DiffSym (Variable a) (Variable b)]

cancelUsAtom :: (Fractional a, Eq a) => Atom a -> Atom a
cancelUsAtom (Atom k ds us exp) =
  case partitionEithers . map separate $ us of
    (ks, us) -> Atom (k * Prelude.product ks) ds us exp
    where
      separate (DiffSym (Variable _) (Constant 0)) = Left 1
      separate (DiffSym (Constant 0) (Variable _)) = Left 0
      separate u@(DiffSym x y) | x == y = Left (1 / 2)
                               | otherwise = Right u

groupifyAtoms :: (Eq a, Num a) => [Atom a] -> [Atom a]
groupifyAtoms [] = []
groupifyAtoms (a : as) = case partition (a `similar`) as of
  ([], rest) -> a : groupifyAtoms rest
  (found, rest) -> let Atom k0 ds us exp = a
                       a' = Atom (k0 + sum (map atomConstant found)) ds us exp
                   in a' : groupifyAtoms rest
  where
    similar (Atom _ ds1 us1 e1) (Atom _ ds2 us2 e2) =
      (e1 == e2) && (ds1 == ds2) && (us1 == us2)    
