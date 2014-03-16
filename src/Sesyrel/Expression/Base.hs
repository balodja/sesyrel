{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Base (
    Expr(..), Term(..) , Atom(..)
  , Symbol(..), DiffSym(..)
  , toList, fromList
  , normalizeDs
  , Substitutable(..)
  , Bundle(..), singletonBundle
  , DeltaBundle(..), UnitBundle(..)
  , expand, deepExpand
  , product, makeSingle
  , groupifyAtoms, cancelUsAtom
  ) where

import Control.Applicative ((<$>))
import qualified Data.Foldable as F (find)

import Data.List (partition, delete)
import Data.Either (partitionEithers)
import Sesyrel.Expression.Ratio (RealInfinite(..))

import Prelude hiding (product)
import qualified Prelude as Prelude (product)

import Data.Set (Set)
import qualified Data.Set as S
  (map, empty, null, union, delete, insert, fromList, toList)
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
  , atomExponent :: !(IntMap a)
  } deriving (Show, Eq)

instance Substitutable Atom where
  substitute v sym (Atom k1 ds us e1) = normalizeDsAtom $
    Atom (k1 * k2) (substitute v sym ds) (substitute v sym us) e2
    where
      (k2, e2) = substituteExp v sym e1

substituteExp :: (RealInfinite a, Eq a) => Int -> Symbol a -> IntMap a -> (a, IntMap a)
substituteExp i (Constant c) vec | value == 0 = (1, vec)
                                 | otherwise = (specialExp (-value * c), IM.delete i vec)
                                   where value = IM.findWithDefault 0 i vec
substituteExp i (Variable j) vec | vi == 0 = (1, vec)
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
fromList [] = ExprN (Term (Atom 0 emptyBundle emptyBundle IM.empty) [])

mapExpr :: Num a => (Term a -> Term a) -> Expr a -> Expr a
mapExpr f = fromList . map f . toList

normalizeDs :: (Num a, Ord a) => Expr a -> Expr a
normalizeDs = mapExpr normalizeDsTerm

normalizeDsTerm :: (Num a, Ord a) => Term a -> Term a
normalizeDsTerm (Term a es) = Term (normalizeDsAtom a) (normalizeDs <$> es)

normalizeDsAtom :: (Num a, Ord a) => Atom a -> Atom a
normalizeDsAtom (Atom k ds us e) = Atom k (DeltaBundle (S.map normalizeDelta (getDeltaBundle ds))) us e

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
product e1 e2 = ExprN (Term (Atom 1 emptyBundle emptyBundle IM.empty) [e1, e2])

productTerm :: (Num a, Ord a) => Term a -> Term a -> Term a
productTerm (Term a1 e1) (Term a2 e2) = Term (productAtom a1 a2) (e1 ++ e2)

productAtom :: (Num a, Ord a) => Atom a -> Atom a -> Atom a
productAtom (Atom k1 d1 u1 e1) (Atom k2 d2 u2 e2) =
  Atom (k1 * k2) (d1 `unionBundle` d2) (u1 `unionBundle` u2) (IM.unionWith (+) e1 e2)

makeSingle :: (Ord a, Bundle b) => Int -> Int -> b a
makeSingle a b = singletonBundle (DiffSym (Variable a) (Variable b))

cancelUsAtom :: (Fractional a, Ord a, RealInfinite a) => Atom a -> Atom a
cancelUsAtom (Atom k1 deltas units expnt) =
  let go k (d@(DiffSym (Variable v) s) : ds) us e =
        let sbstn = substitute v s
            (k', e') = substituteExp v s e
            (k'', ds', us', e'') = go k' (map sbstn ds) (map sbstn us) e'
        in (k'' * k, d : ds', us', e'')
      go k [] us e = (k, [], us, e)
      go _ _ _ _ = error "calcelUsAtom: something strange happened"
      (k2, deltas', units', expnt') = go 1 (toListBundle deltas) (toListBundle units) expnt
      (k3, units'') = cancelUnits (fromListBundle units')
  in Atom (k1 * k2 * k3) (fromListBundle deltas') units'' expnt'

groupifyAtoms :: (Eq a, Num a) => [Atom a] -> [Atom a]
groupifyAtoms [] = []
groupifyAtoms (a : as) = case partition (a `similar`) as of
  ([], rest) -> a : groupifyAtoms rest
  (found, rest) -> let Atom k0 ds us e = a
                       a' = Atom (k0 + sum (map atomConstant found)) ds us e
                   in a' : groupifyAtoms rest
  where
    similar (Atom _ ds1 us1 e1) (Atom _ ds2 us2 e2) =
      (e1 == e2) && (ds1 == ds2) && (us1 == us2)

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
                      deriving (Show, Read, Eq)

instance Substitutable DeltaBundle where
  substitute v sym (DeltaBundle ds) = DeltaBundle $ S.map (substitute v sym) ds

instance Bundle DeltaBundle where
  emptyBundle = DeltaBundle S.empty
  nullBundle (DeltaBundle ds) = S.null ds
  unionBundle (DeltaBundle a) (DeltaBundle b) = DeltaBundle $ S.union a b
  toListBundle (DeltaBundle ds) = S.toList ds
  fromListBundle ds = DeltaBundle $ S.fromList ds
  insertDiff d (DeltaBundle ds) = DeltaBundle $ S.insert d ds
  deleteDiff d (DeltaBundle ds) = DeltaBundle $ S.delete d ds
  findDiff var =
    F.find (\(DiffSym a b) -> a == Variable var || b == Variable var) . getDeltaBundle

normalizeDelta :: DiffSym a -> DiffSym a
normalizeDelta d@(DiffSym (Variable ix) (Variable iy))
  | ix > iy = d
  | otherwise = DiffSym (Variable iy) (Variable ix)
normalizeDelta (DiffSym c@(Constant _) i@(Variable _))
      = DiffSym i c
normalizeDelta d = d

newtype UnitBundle a = UnitBundle {getUnitBundle :: [DiffSym a]}
                     deriving (Show, Read, Eq)

instance Substitutable UnitBundle where
  substitute v sym (UnitBundle us) = UnitBundle $ substitute v sym <$> us

instance Bundle UnitBundle where
  emptyBundle = UnitBundle []
  nullBundle (UnitBundle us) = null us
  unionBundle (UnitBundle a) (UnitBundle b) = UnitBundle (a ++ b)
  toListBundle (UnitBundle us) = us
  fromListBundle us = UnitBundle us
  insertDiff u (UnitBundle us) = UnitBundle $ u : us
  deleteDiff u (UnitBundle us) = UnitBundle $ delete u us
  findDiff var =
    F.find (\(DiffSym a b) -> a == Variable var || b == Variable var) . getUnitBundle

cancelUnits :: (Ord a, Fractional a) => UnitBundle a -> (a, UnitBundle a)
cancelUnits us =
  case partitionEithers . map separate . toListBundle $ us of
    (ks, us') -> (Prelude.product ks, fromListBundle us')
    where
      separate (DiffSym (Variable _) (Constant 0)) = Left 1
      separate (DiffSym (Constant 0) (Variable _)) = Left 0
      separate u@(DiffSym x y) | x == y = Left (1 / 2)
                               | otherwise = Right u
