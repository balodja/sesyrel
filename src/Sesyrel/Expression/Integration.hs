{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Integration (
    integrate
  , integrateM
  ) where

import Sesyrel.Expression.Base
import Sesyrel.Expression.Texify

import Control.Applicative ((<|>))
import Control.Monad.Writer (MonadWriter, runWriter, tell, liftM)

import Data.List (delete)
import Data.Maybe (fromJust, fromMaybe)
import Sesyrel.Expression.Ratio (RealInfinite(..))

import qualified Data.Set as S (empty, delete)
import qualified Data.IntMap.Strict as IM (empty, lookup)
import qualified Data.Foldable as F (Foldable, find)

type Limit a = Symbol a

integrate :: (RealInfinite a, Fractional a, Ord a, Texifiable a) => Expr a -> Int -> Limit a -> Limit a -> Expr a
integrate expr val lo hi = fst . runWriter $ integrateM expr val lo hi

integrateM :: (RealInfinite a, Fractional a, Ord a, Texifiable a, MonadWriter [String] m) => Expr a -> Int -> Limit a -> Limit a -> m (Expr a)
integrateM expr var lo hi = do
  let filterAtoms = filter (\(Atom k _ _ _) -> k /= 0)
      integrateTermM (Term atom _) = do
        tell ["\\paragraph{Atom}", ""]
        let result = integrateAtom atom var lo hi
            exprBefore = ExprN (Term atom [])
            exprAfter = fromList [Term a [] | a <- result]
        tell ["\\begin{dmath*} " ++ "\\int\\limits_0^{+\\infty} "
              ++ texify exprBefore ++ "\\textrm{dx}_{" ++ show (var + 1)
              ++ "} = " ++ texify exprAfter ++ "\\end{dmath*}", ""]
        return result
  atoms' <- liftM concat . mapM integrateTermM . toList . deepExpand $ expr
  let atoms = filterAtoms . groupifyAtoms . filterAtoms . map cancelUsAtom $ atoms'
  return $ fromList [Term a [] | a <- atoms]

integrateAtom :: (RealInfinite a, Fractional a, Ord a) => Atom a -> Int -> Limit a -> Limit a -> [Atom a]
integrateAtom (Atom k ds us exp) var lo hi =
  fromJust $ intEqualLimits <|> intDelta <|> intUnit <|> Just intExp
    where
      intEqualLimits | lo == hi = Just [Atom 0 S.empty [] IM.empty]
                     | otherwise = Nothing
      
      intDelta = case findVar var ds of
        Nothing -> Nothing
        Just d ->
          let sym = calcSubstitution d
              us1 = calcDeltaUnits sym
              a = Atom k (S.delete d ds) (us1 ++ us) exp
          in Just [substituteAtom var sym a]
      
      calcSubstitution (DiffSym (Variable x) (Variable y))
        | x == var = Variable y
        | y == var = Variable x
        | otherwise = error "calcSubstitution: unexpected vars"
      calcSubstitution (DiffSym (Variable x) c@(Constant _))
        | x == var = c
        | otherwise = error "calcSubstitution: unexpected vars"
      calcSubstitution (DiffSym c@(Constant _) (Variable x))
        | x == var = c
        | otherwise = error "calcSubstitution: unexpected vars"
      calcSubstitution _ = error "calcSubstitution: unexpected vars"

      calcDeltaUnits vec = DiffSym vec lo : higher hi
        where
          higher y@(Variable _) = [DiffSym y vec]
          higher y@(Constant c) | c == plusInfinity = []
                                | otherwise = [DiffSym y vec]

      intExp = let lambda = fromMaybe (error "integrateAtom: intExp failed") (IM.lookup var exp)
                   subLimit a (Constant c)
                     | c == plusInfinity = Atom 0 S.empty [] IM.empty
                     | c == 0 = substituteAtom var (Constant 0) a
                     | otherwise = error "intExp: strange constant in limits"
                   subLimit a sym = substituteAtom var sym a
               in [ subLimit (Atom (-k / lambda) ds us exp) hi
                  , subLimit (Atom (k / lambda) ds us exp) lo
                  ]
      
      intUnit = case findVar var us of
        Nothing -> Nothing
        Just u -> Just $ intUnit' u (delete u us)
      intUnit' (DiffSym x y) us | x == Variable var =
        case hi of
          Constant c | c == plusInfinity ->
            let us1 = DiffSym y lo : us
                us2 = DiffSym lo y : us
            in integrateAtom (Atom k ds us1 exp) var y (Constant c)
               ++ integrateAtom (Atom k ds us2 exp) var lo (Constant c)
                     | otherwise -> error "integrateAtom: const at higher limit? no wai"
          higherLimit ->
            let u1 = DiffSym higherLimit y
                u2 = DiffSym y lo
                us1 = u1 : (u2 : us)
                us2 = DiffSym lo y : us
            in integrateAtom (Atom k ds us1 exp) var y hi
               ++ integrateAtom (Atom k ds us2 exp) var lo hi
                       | otherwise =
        case hi of
          Constant c | c == plusInfinity ->
            let us1 = DiffSym x lo : us
            in integrateAtom (Atom k ds us1 exp) var lo x
                     | otherwise -> error "integrateAtom: const at higher limit? no wai"
          higherLimit ->
            let u1 = DiffSym x lo
                u2 = DiffSym higherLimit x
                us1 = u1 : (u2 : us)
                us2 = DiffSym x higherLimit : us
            in integrateAtom (Atom k ds us1 exp) var lo x
               ++ integrateAtom (Atom k ds us2 exp) var lo hi

findVar :: (F.Foldable f, Eq a) => Int -> f (DiffSym a) -> Maybe (DiffSym a)
findVar var = F.find (\(DiffSym a b) -> a == Variable var || b == Variable var)
