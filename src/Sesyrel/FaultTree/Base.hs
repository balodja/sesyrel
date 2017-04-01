{-# LANGUAGE RecursiveDo, GeneralizedNewtypeDeriving #-}

module Sesyrel.FaultTree.Base (
    FaultTree(..)
  , unFaultTree
  , FaultTreeMonadT
  , FaultTreeMonad
  , Variable(..)
  , unVariable
  , runFaultTreeMonadT
  , runFaultTreeMonad
  , FaultTreeNode(..)
  , isDynamic
  , faultTreeVariables
  , unionVariables
  , Factor(..)
  , productFactors
  , variablesM
  , addNodeM
  , lambdaM, constantM
  , notM, andM, orM, xorM
  , twoBitsAdderM, threeBitsAdderM
  , twoRegistersAdderM, literalToRegisterAdderM
  , treeSumM, equalsM, notLessM
  , treeVoterM, foldingVoterM, voterEqualsM
  , naiveVoterM
  , priorityAndOrM
  , switchM
  ) where

import Sesyrel.Texify (Texifiable(..))

import Prelude hiding (Rational)

import Control.Monad.State
import Control.Monad.Identity
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.Maybe (catMaybes)

type FaultTreeMonadT k m = StateT (FaultTree k) m

type FaultTreeMonad k = FaultTreeMonadT k Identity

newtype Variable = Variable Int
                 deriving (Show, Ord, Eq, Num, Enum)

unVariable :: Variable -> Int
unVariable (Variable i) = i

instance Texifiable Variable where
  texify' (Variable i) = texify' i

newtype FaultTree k = FaultTree [(Variable, FaultTreeNode k)]
                  deriving (Show, Eq)

unFaultTree :: FaultTree k -> [(Variable, FaultTreeNode k)]
unFaultTree (FaultTree ps) = ps

data FaultTreeNode k = FaultTreeLambda k
                     | FaultTreeConstant k
                     | FaultTreeNot Variable
                     | FaultTreeAnd Variable Variable
                     | FaultTreeOr Variable Variable
                     | FaultTreeXor Variable Variable
                     | FaultTreePriorityAndOr Variable Variable Variable
                     | FaultTreeSwitch Variable Variable Variable
                     deriving (Show, Eq)

isDynamic :: FaultTree k -> Bool
isDynamic (FaultTree vs) = any isDynamic' $ map snd vs
  where
    isDynamic' (FaultTreeLambda _) = False
    isDynamic' (FaultTreeConstant _) = False
    isDynamic' (FaultTreeNot _) = False
    isDynamic' (FaultTreeAnd _ _) = False
    isDynamic' (FaultTreeOr _ _) = False
    isDynamic' (FaultTreeXor _ _) = False
    isDynamic' (FaultTreePriorityAndOr _ _ _) = True
    isDynamic' (FaultTreeSwitch _ _ _) = True

runFaultTreeMonad :: FaultTreeMonad k a -> (a, FaultTree k)
runFaultTreeMonad = runIdentity . runFaultTreeMonadT

runFaultTreeMonadT :: Monad m => FaultTreeMonadT k m a -> m (a, FaultTree k)
runFaultTreeMonadT a = (\(x, FaultTree s) -> (x, FaultTree $ reverse s)) <$>
                       runStateT a (FaultTree [])

lambdaM, constantM :: Monad m => k -> FaultTreeMonadT k m Variable
lambdaM = addNodeM . FaultTreeLambda
constantM = addNodeM . FaultTreeConstant

notM :: Monad m => Variable -> FaultTreeMonadT k m Variable
notM = addNodeM . FaultTreeNot

andM, orM, xorM :: Monad m => Variable -> Variable -> FaultTreeMonadT k m Variable
andM a b = addNodeM $ FaultTreeAnd a b
orM a b = addNodeM $ FaultTreeOr a b
xorM a b = addNodeM $ FaultTreeXor a b

foldVarsM :: Monad m => (Variable -> Variable -> FaultTreeMonadT k m Variable) ->
             [Variable] -> FaultTreeMonadT k m (Maybe Variable)
foldVarsM _ [] = return Nothing
foldVarsM f vs = foldM (\mb v -> Just <$> maybe (return v) (f v) mb) Nothing vs

naiveVoterM :: (Num k, Monad m) => Int -> [Variable] -> FaultTreeMonadT k m Variable
naiveVoterM k vars = do
  initial <- replicateM k (constantM 0)
  let step voters v = do
        v0 <- constantM 1
        zipWithM (\u u' -> andM v u' >>= orM u) voters (v0 : voters)
  final <- foldM step initial vars
  return $ last final

twoBitsAdderM :: Monad m => Variable -> Variable -> FaultTreeMonadT k m (Variable, Variable)
twoBitsAdderM a b = do
  s <- xorM a b
  c <- andM a b
  return (s, c)

threeBitsAdderM :: Monad m =>
             Variable -> Variable ->
             Variable -> FaultTreeMonadT k m (Variable, Variable)
threeBitsAdderM a b c = do
  aXb <- xorM a b
  s <- xorM aXb c
  aXbc <- andM aXb c
  ab <- andM a b
  c' <- orM ab aXbc -- xorM ab aXbc also possible, as c = ab `xor` bc `xor` ac
  return (s, c')

twoBitsPlusOneAdderM :: Monad m => Variable -> Variable -> FaultTreeMonadT k m (Variable, Variable)
twoBitsPlusOneAdderM a b = do
  notB <- notM b
  s <- xorM a notB
  aNotB <- andM a notB
  c <- xorM aNotB b
  return (s, c)

twoRegistersAdderM :: Monad m => [Variable] -> [Variable] -> FaultTreeMonadT k m ([Variable], Maybe Variable)
twoRegistersAdderM xs' ys' = go xs' ys' Nothing
  where
    go (x : xs) (y : ys) c = do
      (z, c') <- maybe (twoBitsAdderM x y) (threeBitsAdderM x y) c
      (as, c'') <- go xs ys (Just c')
      return (z : as, c'')
    go [] (y : ys) (Just c) = do
      (z, c') <- twoBitsAdderM y c
      (as, c'') <- go [] ys (Just c')
      return (z : as, c'')
    go [] ys c = return (ys, c)
    go xs [] c = go [] xs c


bitToRegisterAdderM :: Monad m => Variable -> [Variable] -> FaultTreeMonadT k m ([Variable], Variable)
bitToRegisterAdderM b reg = (\(dl, cf) -> (dl [], cf)) <$> foldM step (id, b) reg
  where
    step (dl, x) y = do
      (z, c) <- twoBitsAdderM x y
      return (dl . (z :), c)

literalToRegisterAdderM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m ([Variable], Maybe Variable)
literalToRegisterAdderM k' vars = go k' vars Nothing
  where
    go k (x : xs) (Just c) = do
      (s, c') <- if k `mod` 2 == 0
                 then twoBitsAdderM x c
                 else twoBitsPlusOneAdderM x c
      (ss, c'') <- go (k `div` 2) xs (Just c')
      return (s : ss, c'')
    go k (x : xs) Nothing = do
      (s, c') <- if k `mod` 2 == 0
                 then return (x, Nothing)
                 else do {s <- notM x; return (s, Just x)}
      (ss, c'') <- go (k `div` 2) xs c'
      return (s : ss, c'')
    go _ [] c = return ([], c)

extractVariables :: Maybe Variable -> Maybe Variable -> (Variable, Variable)
extractVariables (Just a) (Just c) = (a, c)
extractVariables Nothing _ = error "equalsM, notLessM: 0-order logic, don't"
extractVariables _ Nothing = error "equalsM, notLessM: comparison to (2^order) is not possible"

compareToLiteralM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m (Variable, Variable)
compareToLiteralM k vars = do
  let n = length vars
  (vars', cMb) <- literalToRegisterAdderM (2 ^ n - k) vars
  anyMb <- foldVarsM orM vars'
  return $ extractVariables anyMb cMb

equalsM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m Variable
equalsM k vars = do
  (any', c) <- compareToLiteralM k vars
  notAny' <- notM any'
  notC <- notM c
  andM notAny' notC

notLessM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m Variable
notLessM k vars = do
  (_, c) <- compareToLiteralM k vars
  return c

foldSumM :: (Monad m, Num k)=> Int -> [Variable] -> FaultTreeMonadT k m ([Variable], Variable)
foldSumM n vars = do
  let step (reg, cf) v = do
        (reg', cf') <- bitToRegisterAdderM v reg
        cf'' <- orM cf cf'
        return (reg', cf'')
  accumRegister <- replicateM n (constantM 0)
  accumCf <- constantM 0
  foldM step (accumRegister, accumCf) vars

treeSumM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m ([Variable], Maybe Variable)
treeSumM n vars = do {ps <- split vars; doSum ps}
  where
    split (v1 : v2 : v3 : vs) = do {(s, c) <- threeBitsAdderM v1 v2 v3; r <- split vs; return $ ([s, c], Nothing) : r}
    split [v1, v2] = do {(s, c) <- twoBitsAdderM v1 v2; return [([s, c], Nothing)]}
    split [v1] = return [([v1], Nothing)]
    split [] = return [([], Nothing)]
    doSum [p] = return p
    doSum [] = return ([], Nothing)
    doSum ps = do {ps' <- step ps; doSum ps'}
    step (p1 : p2 : ps) = do {p' <- sumTwo p1 p2; ps' <- step ps; return (p' : ps')}
    step [p] = return [p]
    step [] = return []
    sumTwo (vs1, Nothing) (vs2, Nothing) = do
      (vs3, c3) <- twoRegistersAdderM vs1 vs2
      case c3 of
        Just c -> return $ if length vs3 == n
                           then (vs3, Just c)
                           else (vs3 ++ [c], Nothing)
        Nothing -> return (vs3, Nothing)
    sumTwo (vs1, c1) (vs2, c2) = do
      (vs3, c3) <- twoRegistersAdderM vs1 vs2
      let cs = catMaybes [c1, c2, c3]
      c <- foldVarsM orM cs
      return (vs3, c)

bitsN :: Int -> Int
bitsN k = ceiling . (\x -> log (x :: Double) / log 2) $ 1 + realToFrac k

voterEqualsM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m Variable
voterEqualsM k vars = do
  (sumVars, cfMb) <- treeSumM (bitsN k) vars
  fVar <- equalsM k sumVars
  case cfMb of
    Nothing -> return fVar
    Just cf -> do { notCf <- notM cf; andM notCf fVar }

foldingVoterM :: (Num k, Monad m) => Int -> [Variable] -> FaultTreeMonadT k m Variable
foldingVoterM k vars = do
  (sumVars, cf) <- foldSumM (bitsN k) vars
  fVar <- notLessM k sumVars
  orM fVar cf

treeVoterM :: Monad m => Int -> [Variable] -> FaultTreeMonadT k m Variable
treeVoterM k vars = do
  (sumVars, cfMb) <- treeSumM (bitsN k) vars
  fVar <- notLessM k sumVars
  case cfMb of
    Nothing -> return fVar
    Just cf -> orM fVar cf

priorityAndOrM, switchM :: Monad m => Variable -> Variable -> Variable -> FaultTreeMonadT k m Variable
priorityAndOrM a b c = addNodeM $ FaultTreePriorityAndOr a b c
switchM s a b = addNodeM $ FaultTreeSwitch s a b

addNodeM :: Monad m => FaultTreeNode k -> FaultTreeMonadT k m Variable
addNodeM node = state $ \(FaultTree nodes) ->
  let var = Variable $ length nodes
  in (var, FaultTree $ (var, node) : nodes)

variablesM :: Monad m => FaultTreeMonadT k m [Variable]
variablesM = do
  FaultTree nodes <- get
  return $ [0 .. (fromIntegral $ length nodes - 1)]

faultTreeVariables :: FaultTree k -> [[Variable]]
faultTreeVariables (FaultTree ps) = map (\(v, node) -> v : nodeVariables node) ps
  where
    nodeVariables (FaultTreeLambda _) = []
    nodeVariables (FaultTreeConstant _) = []
    nodeVariables (FaultTreeNot x) = [x]
    nodeVariables (FaultTreeAnd x y) = [x, y]
    nodeVariables (FaultTreeOr x y) = [x, y]
    nodeVariables (FaultTreeXor x y) = [x, y]
    nodeVariables (FaultTreePriorityAndOr x y z) = [x, y, z]
    nodeVariables (FaultTreeSwitch s x y) = [s, x, y]

unionVariables :: [Variable] -> [Variable] -> [Variable]
unionVariables (u : us) (v : vs) | u == v = v : unionVariables us vs
                            | u < v = u : unionVariables us (v : vs)
                            | otherwise = v : unionVariables (u : us) vs
unionVariables [] vs = vs
unionVariables us [] = us

class Texifiable f => Factor f where
  variables :: f -> [Variable]
  eliminate :: Variable -> f -> f
  times :: f -> f -> f
  one :: f
  texifyVariableElimination :: Variable -> f -> Text

productFactors :: Factor f => [f] -> f
productFactors fs = foldl' times one fs
