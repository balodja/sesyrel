{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Base (
    Expr(..), Term(..) , Atom(..)
  , Symbol(..), DiffSym(..)
  , toList, fromList
  , normalizeDs, normalizeUs
  , Substitutable(..)
  , Bundle(..), singletonBundle
  , DeltaBundle(..), UnitBundle(..)
  , expand, deepExpand
  , product, makeSingle
  , groupifyAtoms
  , cancelUsAtom, unifyAtom
  ) where

import Control.Applicative ((<$>))
import qualified Data.Foldable as F (find)
import Data.Monoid ((<>))

import Data.List (sortBy)
import GHC.Exts (build)
import Data.Either (partitionEithers)
import Sesyrel.Expression.Ratio (RealInfinite(..))

import Prelude hiding (product)
import qualified Prelude as Prelude (product)

import Data.Set (Set)
import qualified Data.Set as S
  (map, empty, null, union, delete, insert, fromList, toList)
import Data.SignedMultiset (SignedMultiset)
import qualified Data.SignedMultiset as MS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
  (empty, delete, insert, findWithDefault, unionWith)

data Expr a = ExprC !(Term a) !(Expr a)
            | ExprN !(Term a)
            deriving (Show, Eq)

instance Substitutable Expr where
  substitute v sym = mapExpr (substitute v sym)

data Term a = Term {
    termAtom :: !(Atom a)
  , termExpr :: ![Expr a]
  } deriving (Show, Eq)

instance Substitutable Term where
  substitute v sym (Term a es) = Term (substitute v sym a) (substitute v sym <$> es)

data Atom a = Atom {
    atomConstant :: !a
  , atomDeltas :: !(DeltaBundle a)
  , atomUnits :: !(UnitBundle a)
  , atomIndicators :: !(IndicatorBundle a)
  , atomExponent :: !(IntMap a)
  } deriving (Show, Eq)

instance Substitutable Atom where
  substitute v sym (Atom k1 ds us is e1) = normalizeDsAtom $
    Atom (k1 * k2) (substitute v sym ds) (substitute v sym us) (substitute v sym is) e2
    where
      (k2, e2) = substituteExp v sym e1

substituteExp :: (RealInfinite a, Eq a) => Int -> Symbol a -> IntMap a -> (a, IntMap a)
substituteExp i (Constant c) vec | value == 0 = (1, vec)
                                 | otherwise = (specialExp (-value * c), IM.delete i vec)
                                   where value = IM.findWithDefault 0 i vec
substituteExp i (Variable j) vec | i == j || vi == 0 = (1, vec)
                                 | otherwise = (1, IM.insert j (vi + vj) . IM.delete i $ vec)
                                   where vi = IM.findWithDefault 0 i vec
                                         vj = IM.findWithDefault 0 j vec

data Symbol a = Variable !Int
              | Constant !a
              deriving (Show, Read, Eq)

instance Ord a => Ord (Symbol a) where
  compare (Constant x) (Constant y) = compare x y
  compare (Constant _) (Variable _) = LT
  compare (Variable _) (Constant _) = GT
  compare (Variable i) (Variable j) = compare i j

instance Substitutable Symbol where
  substitute _ _ c@(Constant _) = c
  substitute i s v@(Variable j) | i == j = s
                                | otherwise = v

data DiffSym a = DiffSym {
    diffSymFst :: !(Symbol a)
  , diffSymSnd :: !(Symbol a)
  } deriving (Show, Read, Eq)

instance Ord a => Ord (DiffSym a) where
  compare (DiffSym x1 y1) (DiffSym x2 y2) =
    case compare x1 x2 of
      LT -> LT
      EQ -> compare y1 y2
      GT -> GT

instance Substitutable DiffSym where
  substitute i s (DiffSym x y) = DiffSym (substitute i s x) (substitute i s y)

specialExp :: (RealInfinite a, Eq a) => a -> a
specialExp x | x == 0 = 1 
             | x == plusInfinity = plusInfinity
             | x == minusInfinity = 0
             | otherwise = error "specialExp: non-cardinal exponent"

toList :: Expr a -> [Term a]
toList (ExprC t e) = t : toList e
toList (ExprN t) = [t]

fromList :: Num a => [Term a] -> Expr a
fromList (t : []) = ExprN t
fromList (t : ts) = ExprC t (fromList ts)
fromList [] = ExprN (Term (Atom 0 emptyBundle emptyBundle emptyBundle IM.empty) [])

mapExpr :: Num a => (Term a -> Term a) -> Expr a -> Expr a
mapExpr f = fromList . map f . toList

normalizeDs :: (Num a, Ord a) => Expr a -> Expr a
normalizeDs = mapExpr normalizeDsTerm

normalizeDsTerm :: (Num a, Ord a) => Term a -> Term a
normalizeDsTerm (Term a es) = Term (normalizeDsAtom a) (normalizeDs <$> es)

normalizeDsAtom :: (Num a, Ord a) => Atom a -> Atom a
normalizeDsAtom (Atom k ds us is e) = Atom k (DeltaBundle (S.map normalizeSymmetric (getDeltaBundle ds))) us is e

normalizeUs :: (Num a, Ord a) => Expr a -> Expr a
normalizeUs = mapExpr normalizeUsTerm

normalizeUsTerm :: (Num a, Ord a) => Term a -> Term a
normalizeUsTerm (Term a es) = let (a', es') = normalizeUsAtom a
                              in Term a' (es' ++ (normalizeUs <$> es))

normalizeUsAtom :: (Num a, Ord a) => Atom a -> (Atom a, [Expr a])
normalizeUsAtom (Atom k ds us is e) =
  let (es', us') = partitionEithers . map normalizeUnit . toListBundle $ us
  in (Atom k ds (fromListBundle us') is e, es')

deepExpand :: (Fractional a, Ord a) => Expr a -> Expr a
deepExpand e | isExpandable e = deepExpand (expand e)
             | otherwise = e
  where
    isExpandable = any isExpandableTerm . toList
    isExpandableTerm (Term _ []) = False
    isExpandableTerm _ = True

expand :: (Fractional a, Ord a) => Expr a -> Expr a
expand = fromList . concatMap (toList . expandTerm) . toList

expandTerm :: (Fractional a, Ord a) => Term a -> Expr a
expandTerm (Term a []) = ExprN $ Term a []
expandTerm (Term a es) =
  fromList . map (foldl productTerm (Term a [])) . sequence $ toList <$> es

product :: (Fractional a, Ord a) => Expr a -> Expr a -> Expr a
product e1 e2 = ExprN (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) [e1, e2])

productTerm :: (Fractional a, Ord a) => Term a -> Term a -> Term a
productTerm (Term a1 e1) (Term a2 e2) = Term (productAtom a1 a2) (e1 ++ e2)

productAtom :: (Fractional a, Ord a) => Atom a -> Atom a -> Atom a
productAtom (Atom k1 d1 u1 i1 e1) (Atom k2 d2 u2 i2 e2) =
  Atom (k1 * k2) (d1 `unionBundle` d2) (u1 `unionBundle` u2) (i1 `unionBundle` i2) (IM.unionWith (+) e1 e2)

makeSingle :: (Ord a, Bundle b) => Int -> Int -> b a
makeSingle a b = singletonBundle (DiffSym (Variable a) (Variable b))

cancelUsAtom :: (Fractional a, Ord a, RealInfinite a) => Atom a -> [Atom a]
cancelUsAtom (Atom k1 deltas units inds expnt) =
  let (k2, units') = cancelUnits units
      (k3, inds') = cancelIndicators inds
      atom = Atom (k1 * k2 * k3) deltas (UnitBundle unitsGood) inds' expnt
      (unitsGood, unitsBad) = MS.split 1 (getUnitBundle units')
      makeGood (u, n) = [ Atom 1 emptyBundle (singletonBundle u)
                          emptyBundle IM.empty
                        , Atom (1/(2^n) - 1/2) emptyBundle emptyBundle
                          (singletonBundle u) IM.empty
                        ]
      one = Atom 1 emptyBundle emptyBundle emptyBundle IM.empty
  in map (foldl productAtom atom) . sequence . ([one] :) . map makeGood . MS.toList $ unitsBad

unifyAtom :: (Fractional a, Ord a, RealInfinite a) => Atom a -> Atom a
unifyAtom = unifyByIndicatorAtom . unifyByDeltaAtom

unifyByDeltaAtom :: (Fractional a, Ord a, RealInfinite a) => Atom a -> Atom a
unifyByDeltaAtom (Atom k1 deltas units inds expnt) =
  let goD k (d@(DiffSym (Variable v) s) : ds) us is e =
        let sbstn = substitute v s
            (k', e') = substituteExp v s e
            (k'', ds', us', is', e'') = goD k' (map (normalizeSymmetric . sbstn) ds) (map sbstn us) (map (normalizeSymmetric . sbstn) is) e'
        in (k'' * k, d : ds', us', is', e'')
      goD k [] us is e = (k, [], us, is, e)
      goD _ _ _ _ _ = error "cancelUsAtom: something strange happened"
      (k2, deltas', units', inds', expnt') = goD k1 (toListBundle deltas) (toListBundle units) (toListBundle inds) expnt
  in Atom k2 (fromListBundle deltas') (fromListBundle units') (fromListBundle inds') expnt'

unifyByIndicatorAtom :: (Fractional a, Ord a, RealInfinite a) => Atom a -> Atom a
unifyByIndicatorAtom (Atom k1 deltas units inds expnt) =
  let goI k us (i@(DiffSym (Variable v) s) : is) e =
        let sbstn = substitute v s
            (k', e') = substituteExp v s e
            (k'', us', is', e'') = goI k' (map sbstn us) (map (normalizeSymmetric . sbstn) is) e'
        in (k'' * k, us', i : is', e'')
      goI k us [] e = (k, us, [], e)
      goI _ _ _ _ = error "cancelUsAtom: something strange happened"
      (k2, units', inds', expnt') = goI k1 (toListBundle units) (toListBundle inds) expnt
  in Atom k2 deltas (fromListBundle units') (fromListBundle inds') expnt'

groupifyAtoms :: (Ord a, Num a) => [Atom a] -> [Atom a]
groupifyAtoms = map compact . groupBy similar
  where
    compact as = let (Atom _ ds us is e) = head as
                     k = foldl (\s a -> s + atomConstant a) 0 as
                 in Atom k ds us is e
    similar (Atom _ ds1 us1 is1 e1) (Atom _ ds2 us2 is2 e2) =
      compare e1 e2 <> compare ds1 ds2 <> compare us1 us2 <> compare is1 is2

{-# INLINE groupBy #-}
groupBy :: (a -> a -> Ordering) -> [a] -> [[a]]
groupBy f xs = build (\c n -> groupByFB c n (\x y -> f x y == EQ) (sortBy f xs))

groupByFB :: ([a] -> lst -> lst) -> lst -> (a -> a -> Bool) -> [a] -> lst
groupByFB c n eq xs0 = groupByFBCore xs0
  where groupByFBCore [] = n
        groupByFBCore (x:xs) = c (x:ys) (groupByFBCore zs)
            where (ys, zs) = span (eq x) xs

class Substitutable e where
  substitute :: (RealInfinite a, Ord a) => Int -> Symbol a -> e a -> e a

class Bundle e where
  emptyBundle :: e a
  nullBundle :: e a -> Bool
  unionBundle :: Ord a => e a -> e a -> e a
  toListBundle :: e a -> [DiffSym a]
  fromListBundle :: Ord a => [DiffSym a] -> e a
  insertDiff :: Ord a => DiffSym a -> e a -> e a
  deleteDiff :: Ord a => DiffSym a -> e a -> e a
  findDiff :: (Ord a, Eq a) => Int -> e a -> Maybe (DiffSym a)

singletonBundle :: (Ord a, Bundle b) => DiffSym a -> b a
singletonBundle d = insertDiff d emptyBundle

newtype DeltaBundle a = DeltaBundle {getDeltaBundle :: Set (DiffSym a)}
                      deriving (Show, Read, Eq, Ord)

instance Substitutable DeltaBundle where
  substitute v sym (DeltaBundle ds) = DeltaBundle $ S.map (normalizeSymmetric . substitute v sym) ds

instance Bundle DeltaBundle where
  emptyBundle = DeltaBundle S.empty
  nullBundle (DeltaBundle ds) = S.null ds
  unionBundle (DeltaBundle a) (DeltaBundle b) = DeltaBundle $ S.union a b
  toListBundle (DeltaBundle ds) = S.toList ds
  fromListBundle ds = DeltaBundle . S.fromList . map normalizeSymmetric $ds
  insertDiff d (DeltaBundle ds) = DeltaBundle $ S.insert (normalizeSymmetric d) ds
  deleteDiff d (DeltaBundle ds) = DeltaBundle $ S.delete d ds
  findDiff var =
    F.find (\(DiffSym a b) -> a == Variable var || b == Variable var) . getDeltaBundle

normalizeSymmetric :: DiffSym a -> DiffSym a
normalizeSymmetric d@(DiffSym (Variable ix) (Variable iy))
  | ix > iy = d
  | otherwise = DiffSym (Variable iy) (Variable ix)
normalizeSymmetric (DiffSym c@(Constant _) i@(Variable _))
      = DiffSym i c
normalizeSymmetric d = d

newtype UnitBundle a = UnitBundle {getUnitBundle :: SignedMultiset (DiffSym a)}
                     deriving (Show, Read, Eq, Ord)

instance Substitutable UnitBundle where
  substitute v sym (UnitBundle us) = UnitBundle $ MS.additiveMap (substitute v sym) us

instance Bundle UnitBundle where
  emptyBundle = UnitBundle MS.empty
  nullBundle (UnitBundle us) = MS.null us
  unionBundle (UnitBundle a) (UnitBundle b) = UnitBundle $ MS.additiveUnion a b
  toListBundle (UnitBundle us) = fst . MS.toLists $ us
  fromListBundle us = UnitBundle $ MS.fromLists us []
  insertDiff u (UnitBundle us) = UnitBundle $ MS.insert u us
  deleteDiff u (UnitBundle us) = UnitBundle $ MS.delete u us
  findDiff var =
    F.find (\(DiffSym a b) -> a == Variable var || b == Variable var) . toListBundle

cancelUnits :: (Ord a, Fractional a) => UnitBundle a -> (a, UnitBundle a)
cancelUnits us =
  case partitionEithers . map separate . toListBundle $ us of
    (ks, us') -> (Prelude.product ks, fromListBundle us')
    where
      separate (DiffSym (Variable _) (Constant 0)) = Left 1
      separate (DiffSym (Constant 0) (Variable _)) = Left 0
      separate u@(DiffSym x y) | x == y = Left (1 / 2)
                               | otherwise = Right u

normalizeUnit :: (Num a, Ord a) => DiffSym a -> Either (Expr a) (DiffSym a)
normalizeUnit d@(DiffSym (Variable ix) (Variable iy))
  | ix < iy = Right d
  | otherwise = Left (swapUnit d)
normalizeUnit d@(DiffSym (Constant _) (Variable _))
      = Left (swapUnit d)
normalizeUnit d = Right d


{-# INLINE swapUnit #-}
swapUnit :: (Num a, Ord a) => DiffSym a -> Expr a
swapUnit (DiffSym x y) =
  ExprC (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) []) $
  ExprN (Term (Atom 1 emptyBundle (singletonBundle $ DiffSym y x) emptyBundle IM.empty) [])

newtype IndicatorBundle a = IndicatorBundle {getIndicatorBundle :: Set (DiffSym a)}
                          deriving (Show, Read, Eq, Ord)

instance Substitutable IndicatorBundle where
  substitute v sym (IndicatorBundle is) = IndicatorBundle $ S.map (normalizeSymmetric . substitute v sym) is

instance Bundle IndicatorBundle where
  emptyBundle = IndicatorBundle S.empty
  nullBundle (IndicatorBundle is) = S.null is
  unionBundle (IndicatorBundle a) (IndicatorBundle b) = IndicatorBundle $ S.union a b
  toListBundle (IndicatorBundle is) = S.toList is
  fromListBundle is = IndicatorBundle . S.fromList . map normalizeSymmetric $ is
  insertDiff d (IndicatorBundle is) = IndicatorBundle $ S.insert (normalizeSymmetric d) is
  deleteDiff d (IndicatorBundle is) = IndicatorBundle $ S.delete d is
  findDiff var =
    F.find (\(DiffSym a b) -> a == Variable var || b == Variable var) . getIndicatorBundle

cancelIndicators :: (Ord a, Fractional a) => IndicatorBundle a -> (a, IndicatorBundle a)
cancelIndicators us =
  case partitionEithers . map separate . toListBundle $ us of
    (ks, us') -> (Prelude.product ks, fromListBundle us')
    where
      separate u@(DiffSym x y) | x == y = Left 1
                               | otherwise = Right u
