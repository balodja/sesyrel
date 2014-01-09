{-# LANGUAGE RecursiveDo, FlexibleContexts #-}

import Expression

import qualified Data.Set as S
import Data.List (partition, union, delete)

import Control.Monad.RWS
import Control.Monad.Writer
import Control.Monad.Fix

import Control.Monad (forM_)

type FaultTreeM = RWS Int [String] FaultTree

data FaultTree = FaultTree {
    faultTreeVariables :: Int
  , faultTreeFactors :: [Factor]
  } deriving (Show, Read, Eq)

type Factor = (Expr Rational, [Int])

evalFaultTreeM :: FaultTreeM a -> (a, FaultTree)
evalFaultTreeM a = (\(x, s, _) -> (x, s)) $
                   runRWS fullAction undefined (FaultTree 0 [])
  where
    fullAction = mdo
      x <- local (const n) a
      n <- gets faultTreeVariables
      return x

newVariableM :: FaultTreeM Int
newVariableM = do
  var <- gets faultTreeVariables
  modify $ \fts -> fts { faultTreeVariables = succ (faultTreeVariables fts) }
  return var

addFactorM :: Factor -> FaultTreeM ()
addFactorM factor = modify $ \fts ->
  fts { faultTreeFactors = factor : faultTreeFactors fts }

lambdaM :: Rational -> FaultTreeM Int
lambdaM lambda = do
  var <- newVariableM
  vars <- ask
  let expr = distributionLambda vars var lambda
  addFactorM (expr, [var])
  return var

distributionTwoM :: (Int -> Int -> Int -> Int -> Expr Rational) ->
                    Int -> Int -> FaultTreeM Int
distributionTwoM distr x y = do
  var <- newVariableM
  vars <- ask
  let expr = distr vars var x y
  addFactorM (expr, [x, y, var])
  return var

andM :: Int -> Int -> FaultTreeM Int
andM = distributionTwoM distributionAnd

priorityAndM :: Int -> Int -> FaultTreeM Int
priorityAndM = distributionTwoM distributionPriorityAnd

orM :: Int -> Int -> FaultTreeM Int
orM = distributionTwoM distributionOr

cspM :: Rational -> Int -> FaultTreeM Int
cspM lambda a = do
  b <- newVariableM
  vars <- ask
  let expr = distributionCspLambda vars b lambda a
  addFactorM (expr, [a, b])
  return b

tellFactors :: MonadWriter [String] m => [Factor] -> m ()
tellFactors factors = do
  tell ["\\subsection{Factors}", ""]
  forM_ factors $
    \(expr, _) -> tell ["\\begin{dmath*} " ++ texify expr ++ "\\end{dmath*}", ""]

faultTreeProcess :: MonadWriter [String] m => String -> Maybe [Int] -> FaultTree -> m ()
faultTreeProcess name mbOrder ftree@(FaultTree vars factors) = do
  let lastVar = vars - 1
  tell ["\\section{" ++ name ++ "}", ""]
  expr <- faultTreeIntegrate mbOrder ftree
  [(p, _)] <- factorsEliminateVariable lastVar [(expr, [lastVar])]
  tell ["\\subsection{Results}", ""]
  tell ["$$ p(F) = " ++ texify p ++ " $$", ""]
  let mttf = calcMttf lastVar expr
  tell ["$$ MTTF = " ++ texify mttf ++ " $$", ""]

faultTreeIntegrate :: MonadWriter [String] m => Maybe [Int] -> FaultTree -> m (Expr Rational)
faultTreeIntegrate mbOrder (FaultTree vars factors) = go factors order
  where
    order = maybe [0 .. vars - 2] id mbOrder
    go fs [] = return . fst . head $ fs
    go fs (v : vs) = do
              fs' <- factorsEliminateVariable v fs
              go fs' vs

factorsEliminateVariable :: MonadWriter [String] m => Int -> [Factor] -> m [Factor]
factorsEliminateVariable var factors = do
  tellFactors factors
  tell ["\\subsection{Integration of $x_{" ++ show (succ var) ++ "}$}", ""]
  let (varFactors, restFactors) = partition (elem var . snd) factors
      expr = ExprN (Term (Atom 1 S.empty S.empty Nothing) (map fst varFactors))
  tell ["\\begin{dmath*} " ++ "\\int\\limits_0^{+\\infty} "
        ++ texify expr ++ "\\textrm{dx}_{" ++ show (var + 1)
        ++ "} \\end{dmath*}"
       , "", "$$ = $$", ""]
  let newExpr = integrate expr var Zero Infinity
      newVars = delete var . foldl union [] . map snd $ varFactors
  tell ["\\begin{dmath*} " ++ texify newExpr ++ "\\end{dmath*}", ""]
  return $ ((newExpr, newVars) : restFactors)

main = do
  let doIt = (\(name, mbOrder, ftree) ->
               faultTreeProcess name mbOrder (snd $ evalFaultTreeM ftree))
  writeFile "output.tex" . unlines . execWriter . mapM_ doIt $ trees

trees :: [(String, Maybe [Int], FaultTreeM Int)]
trees =
  [ ("ftree1", Nothing, simpleFaultTreeM1)
  , ("ftree1", Just [0, 3, 1, 2], simpleFaultTreeM1)
  , ("ftree2", Just [0, 2, 1], simpleFaultTreeM2)
  ]

simpleFaultTreeM1 :: FaultTreeM Int
simpleFaultTreeM1 = do
  a <- lambdaM 15.0
  b <- lambdaM 35.0
  andM a b
  c <- lambdaM 3.0
  andM a c

simpleFaultTreeM2 :: FaultTreeM Int
simpleFaultTreeM2 = do
  a <- lambdaM 10.0
  b <- lambdaM 3.0
  c <- priorityAndM a b
  orM b c
