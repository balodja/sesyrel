{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Expression.Distribution (
    calcMttf
  , distributionLambda
  , distributionAnd
  , distributionOr
  , distributionPriorityAndOr
  ) where

import Sesyrel.Expression.Base

import qualified Data.Set as S (null, empty)
import qualified Data.IntMap.Strict as IM (delete, (!), singleton, fromList, empty)
import qualified Data.Foldable as F (all)

calcMttf :: (Eq a, Fractional a) => Int -> Expr a -> a
calcMttf var = sum . map mapTerm . toList
  where
    checkAtom (Atom _ ds us exp) =
      S.null ds && null us && F.all (== 0) (IM.delete var exp)
    mapTerm (Term a@(Atom k _ _ exp) []) | checkAtom a = k / (exp IM.! var) ^ 2
                                         | otherwise =
                                           error "calcMttf: too complex expr"

distributionLambda :: Num a => Int -> a -> Expr a
distributionLambda variable lambda =
  let exp = IM.singleton variable lambda
  in ExprN $ Term (Atom lambda S.empty [] exp) []

-- should not be used
distributionCspLambda :: Num a => Int -> a -> Int -> Expr a
distributionCspLambda varB lambda varA =
  let exp = IM.fromList [(varA, lambda), (varB, -lambda)]
  in ExprN $ Term (Atom lambda S.empty (makeSingleU varB varA) exp) []

distributionAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionAnd x a b =
  let a1 = Atom 1 (makeSingleD x b) (makeSingleU b a) IM.empty
      a2 = Atom 1 (makeSingleD x a) (makeSingleU a b) IM.empty
  in normalizeDs $ ExprC (Term a1 []) (ExprN (Term a2 []))

distributionOr :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionOr x a b =
  let a1 = Atom 1 (makeSingleD x a) (makeSingleU b a) IM.empty
      a2 = Atom 1 (makeSingleD x b) (makeSingleU a b) IM.empty
  in normalizeDs $ ExprC (Term a1 []) (ExprN (Term a2 []))

-- should not be used
distributionPriorityAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionPriorityAnd x a b =
  let atom = Atom 1 (makeSingleD x b) (makeSingleU b a) IM.empty
  in normalizeDs $ ExprN (Term atom [])

distributionPriorityAndOr :: (Num a, Ord a) => Int -> Int -> Int -> Int -> Expr a
distributionPriorityAndOr x a b c =
  let us1 = makeSingleU b a ++ makeSingleU c b
      us2 = makeSingleU b a ++ makeSingleU b c
      a1 = Atom 1 (makeSingleD x b) us1 IM.empty
      a2 = Atom 1 (makeSingleD x c) us2 IM.empty
      a3 = Atom 1 (makeSingleD x c) (makeSingleU a b) IM.empty
  in normalizeDs $ fromList [Term a1 [], Term a2 [], Term a3 []]
