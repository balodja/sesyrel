{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Sesyrel.Expression.Integration (
    integrate
  , integrateM
  ) where

import Sesyrel.Expression.Base
import Sesyrel.Expression.Texify

import Control.Applicative ((<|>))
import Control.Monad.Logger
import Control.Monad.Identity (runIdentity, liftM)
import Data.Monoid ((<>))

import Data.Maybe (fromJust, fromMaybe)
import Sesyrel.Expression.Ratio (RealInfinite(..))

import qualified Data.IntMap.Strict as IM (empty, lookup)

--import qualified Data.Text.Lazy.Builder as TB

type Limit a = Symbol a

integrate :: (RealInfinite a, Fractional a, Ord a, Texifiable a) => Expr a -> Int -> Limit a -> Limit a -> Expr a
integrate expr val lo hi = runIdentity . runNoLoggingT $ integrateM expr val lo hi

integrateM :: (RealInfinite a, Fractional a, Ord a, Texifiable a, MonadLogger m) => Expr a -> Int -> Limit a -> Limit a -> m (Expr a)
integrateM expr var lo hi = do
  let filterAtoms = filter (\(Atom k _ _ _ _) -> k /= 0)
      integrateTermM (Term atom _) = do
        logInfoN "\\paragraph{Atom}\n"
        let integrated = integrateAtom atom var lo hi
            simplified = filterAtoms . concatMap (cancelUsAtom . unifyAtom) $ integrated
            exprBefore = ExprN (Term atom [])
            exprDuring = fromList [Term a [] | a <- integrated]
            exprAfter = fromList [Term a [] | a <- simplified]
        logInfoN ("$\n"
             <> "\\int\\limits_0^{+\\infty} "
             <> texify exprBefore <> "\\textrm{dx}_{" <> texify var
             <> "}\n"
             <> "= " <> texify exprDuring <> "\n"
             <> "= " <> texify exprAfter <> "\n"
             <> "$\n\n")
        return simplified
  atoms' <- liftM concat . mapM integrateTermM . toList . deepExpand $ expr
  let atoms = filterAtoms . groupifyAtoms $ atoms'
  return $ fromList [Term a [] | a <- atoms]

integrateAtom :: (RealInfinite a, Fractional a, Ord a) => Atom a -> Int -> Limit a -> Limit a -> [Atom a]
integrateAtom (Atom k deltas units indctrs expnt) var lo hi =
  fromJust $ intEqualLimits <|> intDelta <|> intUnit <|> intInd <|> Just intExp
    where
      intEqualLimits | lo == hi = Just [Atom 0 emptyBundle emptyBundle emptyBundle IM.empty]
                     | otherwise = Nothing
      
      intDelta = case findDiff var deltas of
        Nothing -> Nothing
        Just d ->
          let sym = calcSubstitution d
              us1 = calcDeltaUnits sym
              a = Atom k (deleteDiff d deltas) (unionBundle us1 units) indctrs expnt
          in Just [substitute var sym a]
      
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

      calcDeltaUnits vec = DiffSym vec lo `insertDiff` higher hi
        where
          higher y@(Variable _) = singletonBundle (DiffSym y vec)
          higher y@(Constant c) | c == plusInfinity = emptyBundle
                                | otherwise = singletonBundle (DiffSym y vec)

      intInd = case findDiff var indctrs of
        Nothing -> Nothing
        Just _ -> Just [Atom 0 emptyBundle emptyBundle emptyBundle IM.empty]

      intExp = let lambda = fromMaybe (error "integrateAtom: intExp failed") (IM.lookup var expnt)
                   subLimit a (Constant c)
                     | c == plusInfinity = Atom 0 emptyBundle emptyBundle emptyBundle IM.empty
                     | c == 0 = substitute var (Constant 0) a
                     | otherwise = error "intExp: strange constant in limits"
                   subLimit a sym = substitute var sym a
               in [ subLimit (Atom (-k / lambda) deltas units indctrs expnt) hi
                  , subLimit (Atom (k / lambda) deltas units indctrs expnt) lo
                  ]
      
      intUnit = case findDiff var units of
        Nothing -> Nothing
        Just u -> Just $ intUnit' u (deleteDiff u units)
      intUnit' (DiffSym x y) us | x == Variable var =
        case hi of
          Constant c | c == plusInfinity ->
            let us1 = DiffSym y lo `insertDiff` us
                us2 = DiffSym lo y `insertDiff` us
            in integrateAtom (Atom k deltas us1 indctrs expnt) var y (Constant c)
               ++ integrateAtom (Atom k deltas us2 indctrs expnt) var lo (Constant c)
                     | otherwise -> error "integrateAtom: const at higher limit? no wai"
          higherLimit ->
            let u1 = DiffSym higherLimit y
                u2 = DiffSym y lo
                us1 = u1 `insertDiff` (u2 `insertDiff` us)
                us2 = DiffSym lo y `insertDiff` us
            in integrateAtom (Atom k deltas us1 indctrs expnt) var y hi
               ++ integrateAtom (Atom k deltas us2 indctrs expnt) var lo hi
                       | otherwise =
        case hi of
          Constant c | c == plusInfinity ->
            let us1 = DiffSym x lo `insertDiff` us
            in integrateAtom (Atom k deltas us1 indctrs expnt) var lo x
                     | otherwise -> error "integrateAtom: const at higher limit? no wai"
          higherLimit ->
            let u1 = DiffSym x lo
                u2 = DiffSym higherLimit x
                us1 = u1 `insertDiff` (u2 `insertDiff` us)
                us2 = DiffSym x higherLimit `insertDiff` us
            in integrateAtom (Atom k deltas us1 indctrs expnt) var lo x
               ++ integrateAtom (Atom k deltas us2 indctrs expnt) var lo hi
