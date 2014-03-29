{-# LANGUAGE FlexibleContexts #-}

module Sesyrel.Distribution (
    calcMttf
  , distributionLambda
  , distributionAnd
  , distributionOr
  , distributionPriorityAndOr
  , distributionSwitch
  , Factor
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

import qualified Data.IntMap.Strict as IM (delete, lookup, singleton, empty)
import Data.Maybe (fromMaybe)
import qualified Data.Foldable as F (all)

type Factor = (Expr Rational, [Int])

calcMttf :: (Eq a, Fractional a) => Int -> Expr a -> a
calcMttf var = sum . map mapTerm . toList
  where
    checkAtom (Atom _ ds us is expnt) =
      nullBundle ds && nullBundle us && nullBundle is && F.all (== 0) (IM.delete var expnt)
    mapTerm (Term a@(Atom k _ _ _ expnt) []) | checkAtom a =
      k / (fromMaybe (error "calcMttf: lookup fail") (IM.lookup var expnt)) ^ (2 :: Integer)
                                           | otherwise =
                                             error "calcMttf: too complex expr"
    mapTerm (Term _ _) = error "calcMttf: expr is not atomized"

calcDistribution :: (Ord a, Fractional a, Texifiable a, RealInfinite a) => Int -> Expr a -> Expr a
calcDistribution v e = substitute (-1) (Variable v) $ integrate e v (Constant 0) (Variable (-1))

distributionLambda :: Num a => Int -> a -> Expr a
distributionLambda variable lambda =
  let expnt = IM.singleton variable lambda
  in ExprN $ Term (Atom lambda emptyBundle emptyBundle emptyBundle expnt) []

{-
-- should not be used
distributionCspLambda :: (Num a, Ord a) => Int -> a -> Int -> Expr a
distributionCspLambda varB lambda varA =
  let expnt = IM.fromList [(varA, lambda), (varB, -lambda)]
  in ExprN $ Term (Atom lambda emptyBundle (makeSingle varB varA) expnt) []
-}

distributionAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionAnd x a b =
  let a1 = Atom 1 (makeSingle x b) (makeSingle b a) emptyBundle IM.empty
      a2 = Atom 1 (makeSingle x a) (makeSingle a b) emptyBundle IM.empty
  in ExprC (Term a1 []) (ExprN (Term a2 []))

distributionOr :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionOr x a b =
  let a1 = Atom 1 (makeSingle x a) (makeSingle b a) emptyBundle IM.empty
      a2 = Atom 1 (makeSingle x b) (makeSingle a b) emptyBundle IM.empty
  in ExprC (Term a1 []) (ExprN (Term a2 []))

{-
-- should not be used
distributionPriorityAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionPriorityAnd x a b =
  let atom = Atom 1 (makeSingle x b) (makeSingle b a) IM.empty
  in ExprN (Term atom [])
-}

distributionPriorityAndOr :: (Num a, Ord a) => Int -> Int -> Int -> Int -> Expr a
distributionPriorityAndOr x a b c =
  let us1 = makeSingle b a `unionBundle` makeSingle c b
      us2 = makeSingle b a `unionBundle` makeSingle b c
      a1 = Atom 1 (makeSingle x b) us1 emptyBundle IM.empty
      a2 = Atom 1 (makeSingle x c) us2 emptyBundle IM.empty
      a3 = Atom 1 (makeSingle x c) (makeSingle a b) emptyBundle IM.empty
  in fromList [Term a1 [], Term a2 [], Term a3 []]

distributionSwitch :: (Num a, Ord a) => Int -> Int -> Int -> Int -> Expr a
distributionSwitch x s a b =
  let us1 = makeSingle s a `unionBundle` makeSingle b a
      us2 = makeSingle s a `unionBundle` makeSingle a b
      a1 = Atom 1 (makeSingle x b) us1 emptyBundle IM.empty
      a2 = Atom 1 (makeSingle x a) us2 emptyBundle IM.empty
      a3 = Atom 1 (makeSingle x a) (makeSingle a s) emptyBundle IM.empty
  in fromList [Term a1 [], Term a2 [], Term a3 []]

factorsTell :: MonadWriter [String] m => [Factor] -> m ()
factorsTell factors = do
  tell ["\\subsection{Factors}", ""]
  let fellers = map (\(expr, _) -> tell ["$ " ++ texify expr ++ " $"]) factors
  sequence_ (intersperse (tell [","]) fellers)

factorsSimpleProcess :: MonadWriter [String] m => String -> Either [Int] [Int] -> [Factor] -> m ([Factor], Maybe (Expr Rational))
factorsSimpleProcess name vv joint = do
  tell ["\\section{" ++ name ++ "}", ""]
  marginal <- either
              (\vs -> factorsMarginalize vs joint)
              (\vs -> factorsEliminate vs False joint) vv
  tell ["\\subsection{More elimination?}", ""]
  constant <- factorsMarginalize [] marginal
  let p = deepExpand . foldl1 product .  map fst $ constant
  tell ["\\subsection{Results}", ""]
  tell ["$ F(\\infty) = " ++ texify p ++ " $"]
  distr <- case vv of
    Left [lastVar] -> do
      let marginalized = deepExpand . foldl1 product . map fst $ marginal
          mttf = fromRational $ calcMttf lastVar marginalized
          distr = calcDistribution lastVar marginalized
      tell [", $ F(x_{" ++ show lastVar ++ "}) = " ++ texify distr ++ "$ , $ MTTF = " ++ texifyDoubleE 3 mttf ++ " $"]
      return (Just distr)
    _ -> return Nothing
  tell [""]
  return (marginal, distr)

factorsEliminate :: MonadWriter [String] m => [Int] -> Bool -> [Factor] -> m [Factor]
factorsEliminate elims algo factors =
  do
    let order = if algo then findOrdering Nothing elims (map snd factors) else elims
    tell ["Elimination order: " ++
          intercalate ", " (map show order), ""]
    let cliques = pretend order (map snd factors)
    tell ["Clique history: "]
    forM_ cliques $ \cs -> tell ["\\\\ $ " ++ intercalate "," (map show cs) ++ " $"]
    tell [""]
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
      expr = ExprN (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) (map fst varFactors))
  tell ["$ " ++ "\\int\\limits_0^{+\\infty} "
        ++ texify expr ++ "\\textrm{dx}_{" ++ show var
        ++ "} = \\ldots $", ""]
  newExpr <- integrateM expr var (Constant 0) (Constant plusInfinity)
  let newVars = delete var . foldl union [] . map snd $ varFactors
  tell ["", "\\paragraph{Integration result}", "$ \\ldots = " ++ texify newExpr ++ " $", ""]
  return $ (newExpr, newVars) : restFactors
