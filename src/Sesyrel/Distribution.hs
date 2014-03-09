{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Distribution (
    calcMttf
  , distributionLambda
  , distributionAnd
  , distributionOr
  , distributionPriorityAndOr
  , Factor(..)
  , factorsTell
  , factorsSimpleProcess
  , factorsEliminate
  , factorsMarginalize
  , factorsEliminateVariable
  ) where

import Sesyrel.Expression
import Sesyrel.Elimination

import Control.Monad.Writer

import Prelude hiding (product, Rational)
import Data.List (intercalate, intersperse, nub, sort, union, partition, delete, (\\))

import qualified Data.IntMap.Strict as IM (delete, lookup, singleton, fromList, empty)
import Data.Maybe (fromMaybe)
import qualified Data.Foldable as F (all)

type Factor = (Expr Rational, [Int])

calcMttf :: (Eq a, Fractional a) => Int -> Expr a -> a
calcMttf var = sum . map mapTerm . toList
  where
    checkAtom (Atom _ ds us exp) =
      nullBundle ds && nullBundle us && F.all (== 0) (IM.delete var exp)
    mapTerm (Term a@(Atom k _ _ exp) []) | checkAtom a = k / (fromMaybe (error "calcMttf: lookup fail") (IM.lookup var exp)) ^ 2
                                         | otherwise =
                                           error "calcMttf: too complex expr"

distributionLambda :: Num a => Int -> a -> Expr a
distributionLambda variable lambda =
  let exp = IM.singleton variable lambda
  in ExprN $ Term (Atom lambda emptyBundle emptyBundle exp) []

-- should not be used
distributionCspLambda :: (Num a, Ord a) => Int -> a -> Int -> Expr a
distributionCspLambda varB lambda varA =
  let exp = IM.fromList [(varA, lambda), (varB, -lambda)]
  in ExprN $ Term (Atom lambda emptyBundle (makeSingle varB varA) exp) []

distributionAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionAnd x a b =
  let a1 = Atom 1 (makeSingle x b) (makeSingle b a) IM.empty
      a2 = Atom 1 (makeSingle x a) (makeSingle a b) IM.empty
  in normalizeDs $ ExprC (Term a1 []) (ExprN (Term a2 []))

distributionOr :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionOr x a b =
  let a1 = Atom 1 (makeSingle x a) (makeSingle b a) IM.empty
      a2 = Atom 1 (makeSingle x b) (makeSingle a b) IM.empty
  in normalizeDs $ ExprC (Term a1 []) (ExprN (Term a2 []))

-- should not be used
distributionPriorityAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionPriorityAnd x a b =
  let atom = Atom 1 (makeSingle x b) (makeSingle b a) IM.empty
  in normalizeDs $ ExprN (Term atom [])

distributionPriorityAndOr :: (Num a, Ord a) => Int -> Int -> Int -> Int -> Expr a
distributionPriorityAndOr x a b c =
  let us1 = makeSingle b a `unionBundle` makeSingle c b
      us2 = makeSingle b a `unionBundle` makeSingle b c
      a1 = Atom 1 (makeSingle x b) us1 IM.empty
      a2 = Atom 1 (makeSingle x c) us2 IM.empty
      a3 = Atom 1 (makeSingle x c) (makeSingle a b) IM.empty
  in normalizeDs $ fromList [Term a1 [], Term a2 [], Term a3 []]

factorsTell :: MonadWriter [String] m => [Factor] -> m ()
factorsTell factors = do
  tell ["\\subsection{Factors}", ""]
  let fellers = map (\(expr, _) -> tell ["$ " ++ texify expr ++ " $"]) factors
  sequence_ (intersperse (tell [","]) fellers)

factorsSimpleProcess :: MonadWriter [String] m => String -> Either [Int] [Int] -> [Factor] -> m ()
factorsSimpleProcess name vv joint = do
  tell ["\\section{" ++ name ++ "}", ""]
  marginal <- either
              (\vs -> factorsMarginalize vs joint)
              (\vs -> factorsEliminate vs False joint) vv
  tell ["\\subsection{More elimination?}", ""]
  constant <- factorsMarginalize [] marginal
  let p = deepExpand . foldl1 product .  map fst $ constant
  tell ["\\subsection{Results}", ""]
  tell ["$ p(F) = " ++ texify p ++ " $"]
  case vv of
    Left [lastVar] -> do
      let mttf = calcMttf lastVar (deepExpand . foldl1 product . map fst $ marginal)
      tell [", $ MTTF = " ++ texify mttf ++ " $"]
    _ -> return ()
  tell [""]

factorsEliminate :: MonadWriter [String] m => [Int] -> Bool -> [Factor] -> m [Factor]
factorsEliminate elims algo factors =
  do
    let order = if algo then findOrdering elims (map snd factors) else elims
    tell ["Elimination order: " ++
          intercalate ", " (map show order), ""]
    go factors order
  where
    go fs [] = return fs
    go fs (v : vs) = do
              fs' <- factorsEliminateVariable v fs
              go fs' vs

factorsMarginalize :: MonadWriter [String] m => [Int] -> [Factor] -> m [Factor]
factorsMarginalize margs factors =
  let vars = nub . sort $ foldl union [] (map snd factors)
  in factorsEliminate (vars \\ margs) True factors

factorsEliminateVariable :: MonadWriter [String] m => Int -> [Factor] -> m [Factor]
factorsEliminateVariable var factors = do
  factorsTell factors
  tell ["\\subsection{Integration of $x_{" ++ show var ++ "}$}", ""]
  let (varFactors, restFactors) = partition (elem var . snd) factors
      expr = ExprN (Term (Atom 1 emptyBundle emptyBundle IM.empty) (map fst varFactors))
  tell ["$ " ++ "\\int\\limits_0^{+\\infty} "
        ++ texify expr ++ "\\textrm{dx}_{" ++ show var
        ++ "} = \\ldots $", ""]
  newExpr <- integrateM expr var (Constant 0) (Constant plusInfinity)
  let newVars = delete var . foldl union [] . map snd $ varFactors
  tell ["", "\\paragraph{Integration result}", "$ \\ldots = " ++ texify newExpr ++ " $", ""]
  return $ (newExpr, newVars) : restFactors