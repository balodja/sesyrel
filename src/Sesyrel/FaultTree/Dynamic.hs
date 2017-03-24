{-# LANGUAGE OverloadedStrings #-}
module Sesyrel.FaultTree.Dynamic (
    compileDynamicFaultTree
  , logDynamicFactorInfo
  , DynamicFactor(..)
  , dynamicFactorExpr
  ) where

import Sesyrel.FaultTree.Base hiding (Variable)
import qualified Sesyrel.FaultTree.Base as F (Variable(..))
import Sesyrel.Expression
import Sesyrel.Texify

import Control.Monad (forM_)
import Control.Monad.Logger
import Data.Monoid ((<>))

import qualified Data.IntMap.Strict as IM (delete, lookup, singleton, empty)
import Data.Maybe (fromMaybe)

import Data.List (delete, sort)

--data DynamicFactor = DynamicFactor (Expr Rational, [F.Variable])
data DynamicFactor = DynamicFactor [F.Variable] (Expr Rational)

dynamicFactorExpr :: DynamicFactor -> Expr Rational
dynamicFactorExpr (DynamicFactor _ e) = e

instance Texifiable DynamicFactor where
  texify' (DynamicFactor _ expr) = "$ " <> texify' expr <> " $ "

instance Factor DynamicFactor where
  variables (DynamicFactor vs _) = vs
  eliminate var (DynamicFactor vars expr) | not $ var `elem` vars = DynamicFactor vars expr
                                          | otherwise = DynamicFactor vars' expr'
   where
    vars' = delete var vars
    expr' = integrate expr (unVariable var) (Constant 0) (Constant plusInfinity)
  times (DynamicFactor vs1 expr1) (DynamicFactor vs2 expr2) =
    DynamicFactor (vs1 `unionVariables` vs2) $ productExpression [expr1, expr2]
  one = DynamicFactor [] $ productExpression []
  
  texifyVariableElimination (F.Variable var) (DynamicFactor _ expr) =
    "$ " <> "\\int\\limits_0^{+\\infty} "
    <> texify expr <> "\\textrm{dx}_{" <> texify var
    <> "}$ "

productExpression :: Num a => [Expr a] -> Expr a
productExpression es = ExprN (Term (Atom 1 emptyBundle emptyBundle emptyBundle IM.empty) es)

logDynamicFactorInfo :: MonadLogger m => DynamicFactor -> [Double] -> m ()
logDynamicFactorInfo (DynamicFactor [F.Variable var] expr) points = do
  let mttf = fromRational $ calcMttf var expr
      distr = calcDistribution var expr
      texifyPoint p v =
        logInfoN ("\\\\  $ F(" <> texifyDoubleE 3 p <> ") = " <> texifyDoubleE 3 v <> " $\n")
  logInfoN "\n\\subsection{Some information}\n\n"
  logInfoN $ "$ F(x_{" <> texify var <> "}) = " <> texify distr <> "$ , $ MTTF = " <> texifyDoubleE 3 mttf <> " $\n"
  let distr' = mapExprType fromRational distr
  logInfoN "\nEvaluation of some points in distribution:\n"
  forM_ points $ \p ->
    texifyPoint p (evalExpr distr' (IM.singleton var p))
  logInfoN "\n"
logDynamicFactorInfo _ _ = return ()

calcMttf :: (Eq a, Fractional a) => Int -> Expr a -> a
calcMttf var = sum . map mapTerm . toList
  where
    checkAtom (Atom _ ds us is expnt) =
      nullBundle ds && nullBundle us && nullBundle is && all (== 0) (IM.delete var expnt)
    mapTerm (Term a@(Atom k _ _ _ expnt) []) | checkAtom a =
      k / (fromMaybe (error "calcMttf: lookup fail") (IM.lookup var expnt)) ^ (2 :: Integer)
                                           | otherwise =
                                             error "calcMttf: too complex expr"
    mapTerm (Term _ _) = error "calcMttf: expr is not atomized"

calcDistribution :: (Ord a, Fractional a, Texifiable a, RealInfinite a) => Int -> Expr a -> Expr a
calcDistribution v e = substitute (-1) (Variable v) $ integrate e v (Constant 0) (Variable (-1))

distributionLambda :: Int -> a -> Expr a
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

compileDynamicFaultTree :: FaultTree Rational -> [DynamicFactor]
compileDynamicFaultTree (FaultTree ft) = map reNode ft
  where
    u = unVariable
    reNode :: (F.Variable, FaultTreeNode Rational) -> DynamicFactor
    reNode (x, FaultTreeLambda k) = DynamicFactor [x] $ distributionLambda (u x) k
    reNode (x, FaultTreeAnd a b) = DynamicFactor (sort [x, a, b]) $ distributionAnd (u x) (u a) (u b)
    reNode (x, FaultTreeOr a b) = DynamicFactor (sort [x, a, b]) $ distributionOr (u x) (u a) (u b)
    reNode (x, FaultTreePriorityAndOr a b c) = DynamicFactor (sort [x, a, b, c]) $ distributionPriorityAndOr (u x) (u a) (u b) (u c)
    reNode (x, FaultTreeSwitch s a b) = DynamicFactor (sort [x, s, a, b]) $ distributionSwitch (u x) (u s) (u a) (u b)
