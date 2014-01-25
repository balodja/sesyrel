{-# LANGUAGE FlexibleContexts #-}

module Expression where

import Control.Applicative
import Control.Monad.Writer

import Data.List (intersperse, partition, union, delete)
import Data.Maybe (fromJust, listToMaybe)
import Data.Either (partitionEithers)
import Ratio (Ratio, RealInfinite(..), numerator, denominator)

import Data.Set (Set)
import qualified Data.Set as S
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.Foldable as F (Foldable, all, find)

data Expr a = ExprC (Term a) (Expr a)
            | ExprN (Term a)
            deriving (Show, Eq)

data Term a = Term {
    termAtom :: Atom a
  , termExpr :: [Expr a]
  } deriving (Show, Eq)

data Atom a = Atom {
    atomConstant :: a
  , atomDeltas :: Set (DiffSym a)
  , atomUnits :: [DiffSym a]
  , atomExponent :: IntMap a
  } deriving (Show, Eq)

data Symbol a = Variable !Int
              | Constant !a
              deriving (Show, Eq)

instance Ord a => Ord (Symbol a) where
  compare (Constant x) (Constant y) = compare x y
  compare (Constant _) (Variable _) = LT
  compare (Variable _) (Constant _) = GT
  compare (Variable i) (Variable j) = compare i j

data DiffSym a = DiffSym {
    diffSymFst :: !(Symbol a)
  , diffSymSnd :: !(Symbol a)
  } deriving (Show, Eq)

instance Ord a => Ord (DiffSym a) where
  compare (DiffSym x1 y1) (DiffSym x2 y2) =
    case compare x1 x2 of
      LT -> LT
      EQ -> compare y1 y2
      GT -> GT

specialExp :: (RealInfinite a, Eq a) => a -> a
specialExp x | x == 0 = 1 
             | x == plusInfinity = plusInfinity
             | x == minusInfinity = 0
             | otherwise = error "specialExp: non-cardinal exponent"

toList :: Expr a -> [Term a]
toList (ExprC t e) = t : toList e
toList (ExprN t) = [t]

fromList :: [Term a] -> Expr a
fromList (t : []) = ExprN t
fromList (t : ts) = ExprC t (fromList ts)
fromList [] = error "fromList: term list is empty"

mapExpr :: (Term a -> Term a) -> Expr a -> Expr a
mapExpr f = fromList . map f . toList

class Texifiable a where
  texify :: a -> String

instance Texifiable Integer where
  texify = show

instance Texifiable Int where
  texify = show

instance Texifiable Double where
  texify = show

instance (Integral a, Texifiable a) => Texifiable (Ratio a) where
  texify z = let y = denominator z
                 x = numerator z
                 infty x | x > 0 = "+\\infty"
                         | x < 0 = "-\\infty"
                         | otherwise = "\\bot"
                 check 1 = texify x
                 check 0 = infty x
                 check y = "\\frac{" ++ texify x ++ "}{" ++ texify y ++ "}"
             in check y

instance (Num a, Ord a, Texifiable a) => Texifiable (Expr a) where
  texify expr = let terms = texifyTerm <$> toList expr
                    signs = fst <$> terms
                    signStrs = (if head signs == '+' then "" else "-")
                               : [ ' ' : s : " " | s <- tail signs ]
                in concat $ zipWith (++) signStrs (snd <$> terms)

instance Texifiable a => Texifiable (Symbol a) where
  texify (Variable i) = "x_{" ++ texify i ++ "}"
  texify (Constant x) = texify x

instance Texifiable a => Texifiable (DiffSym a) where
  texify (DiffSym x y) = texify x ++ " - " ++ texify y

texifyTerm :: (Num a, Ord a, Texifiable a) => Term a -> (Char, String)
texifyTerm (Term a es) | isOne a && (not $ null exprs) = (fst (texifyAtom a), exprs)
                       | otherwise = (sign, atom ++ delimiter ++ exprs)
    where
      (sign, atom) = texifyAtom a
      isOne (Atom k ds us exp) = abs k == 1 && S.null ds && null us && F.all (== 0) exp
      delimiter = if null atom || null exprs then "" else " "
      exprs = concat . intersperse " " $ texifyAndParen <$> es
      texifyAndParen e@(ExprC _ _) = "\\left( " ++ texify e ++ " \\right)"
      texifyAndParen e@(ExprN _) = texify e

texifyAtom :: (Num a, Ord a, Texifiable a) => Atom a -> (Char, String)
texifyAtom (Atom k deltas units exponent)
  | S.null deltas
    && null units
    && F.all (== 0) exponent = (sign, texify absK)
  | otherwise =
    (,) sign $
    (if absK == 1 then [] else texify absK)
      ++ (concat . intersperse " " . map texifyDelta . S.toList $ deltas)
      ++ (concat . intersperse " " . map texifyUnit $ units)
      ++ texifyExponent (IM.map negate exponent)
        where
          absK = abs k
          sign = if signum k == 1 then '+' else '-'
          nullCheck [] = "0"
          nullCheck s = s
          texifyDelta d = "\\delta(" ++ texify d ++ ")"
          texifyUnit u = "\\theta(" ++ texify u ++ ")"
          texifyExponent e = let vf = texifyVarForm e
                             in if null vf then [] else "e^{" ++ vf ++ "}"

texifyVarForm :: (Num a, Ord a, Texifiable a) => IntMap a -> String
texifyVarForm = cutPlus . concat . map texifyVar . IM.toList
  where
    texifyVar (n, v) | v == 0 = ""
                     | otherwise = sign v : (showNum v ++ "x_{" ++ show n ++ "}")
    sign v = if v > 0 then '+' else '-'
    showNum x = let ax = abs x in if ax == 1 then [] else texify ax
    cutPlus ('+' : s) = s
    cutPlus s = s

normalizeDs :: (Num a, Ord a) => Expr a -> Expr a
normalizeDs = mapExpr normalizeDsTerm

normalizeDsTerm :: (Num a, Ord a) => Term a -> Term a
normalizeDsTerm (Term a es) = Term (normalizeDsAtom a) (normalizeDs <$> es)

normalizeDsAtom :: (Num a, Ord a) => Atom a -> Atom a
normalizeDsAtom (Atom k ds us e) = Atom k (S.map swapDelta ds) us e
  where
    swapDelta d@(DiffSym (Variable ix) (Variable iy))
      | ix < iy = d
      | otherwise = DiffSym (Variable iy) (Variable ix)
    swapDelta d@(DiffSym c@(Constant _) i@(Variable _))
      = DiffSym i c
    swapDelta d = d

substitute :: (RealInfinite a, Ord a) => Int -> Symbol a -> Expr a -> Expr a
substitute v sym = mapExpr (substituteTerm v sym)

substituteTerm :: (RealInfinite a, Ord a) => Int -> Symbol a -> Term a -> Term a
substituteTerm v sym (Term a es) = Term (substituteAtom v sym a) (substitute v sym <$> es)

substituteAtom :: (RealInfinite a, Ord a) => Int -> Symbol a -> Atom a -> Atom a
substituteAtom v sym (Atom k1 ds us e1) = normalizeDsAtom $
  Atom (k1 * k2) (S.map (substituteDiffSym v sym) ds) (substituteDiffSym v sym <$> us) e2
  where
    (k2, e2) = substituteExp v sym e1

substituteDiffSym :: Int -> Symbol a -> DiffSym a -> DiffSym a
substituteDiffSym i s (DiffSym x y) = DiffSym (substituteSym i s x) (substituteSym i s y)

substituteSym :: Int -> Symbol a -> Symbol a -> Symbol a
substituteSym i s c@(Constant _) = c
substituteSym i s v@(Variable j) | i == j = s
                                 | otherwise = v

substituteExp :: (RealInfinite a, Eq a) => Int -> Symbol a -> IntMap a -> (a, IntMap a)
substituteExp i (Constant c) vec | value == 0 = (1, vec)
                                 | otherwise = (specialExp (-value * c), IM.delete i vec)
                                   where value = IM.findWithDefault 0 i vec
substituteExp i (Variable j) vec | vi == 0 = (1, vec)
                                 | otherwise = (1, IM.insert j (vi + vj) . IM.delete i $ vec)
                                   where vi = IM.findWithDefault 0 i vec
                                         vj = IM.findWithDefault 0 j vec              

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
product e1 e2 = ExprN (Term (Atom 1 S.empty [] IM.empty) [e1, e2])

productTerm :: (Num a, Ord a) => Term a -> Term a -> Term a
productTerm (Term a1 e1) (Term a2 e2) = Term (productAtom a1 a2) (e1 ++ e2)

productAtom :: (Num a, Ord a) => Atom a -> Atom a -> Atom a
productAtom (Atom k1 d1 u1 e1) (Atom k2 d2 u2 e2) =
  Atom (k1 * k2) (S.union d1 d2) (u1 ++ u2) (IM.unionWith (+) e1 e2)

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
  let a1 = normalizeDsAtom $ Atom 1 (makeSingleD x b) (makeSingleU b a) IM.empty
      a2 = normalizeDsAtom $ Atom 1 (makeSingleD x a) (makeSingleU a b) IM.empty
  in ExprC (Term a1 []) (ExprN (Term a2 []))

distributionOr :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionOr x a b =
  let a1 = normalizeDsAtom $ Atom 1 (makeSingleD x a) (makeSingleU b a) IM.empty
      a2 = normalizeDsAtom $ Atom 1 (makeSingleD x b) (makeSingleU a b) IM.empty
  in ExprC (Term a1 []) (ExprN (Term a2 []))

-- should not be used
distributionPriorityAnd :: (Num a, Ord a) => Int -> Int -> Int -> Expr a
distributionPriorityAnd x a b =
  let atom = normalizeDsAtom $ Atom 1 (makeSingleD x b) (makeSingleU b a) IM.empty
  in ExprN (Term atom [])

distributionPriorityAndOr :: (Num a, Ord a) => Int -> Int -> Int -> Int -> Expr a
distributionPriorityAndOr x a b c =
  let us1 = makeSingleU b a ++ makeSingleU c b
      us2 = makeSingleU b a ++ makeSingleU b c
      a1 = normalizeDsAtom $ Atom 1 (makeSingleD x b) us1 IM.empty
      a2 = normalizeDsAtom $ Atom 1 (makeSingleD x c) us2 IM.empty
      a3 = normalizeDsAtom $ Atom 1 (makeSingleD x c) (makeSingleU a b) IM.empty
  in fromList [Term a1 [], Term a2 [], Term a3 []]

makeSingleD :: Int -> Int -> Set (DiffSym a)
makeSingleD a b = S.singleton (DiffSym (Variable a) (Variable b))

makeSingleU :: Int -> Int -> [DiffSym a]
makeSingleU a b = [DiffSym (Variable a) (Variable b)]

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
      intEqualLimits | lo == hi = Just $ [Atom 0 S.empty [] IM.empty]
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

      intExp = let lambda = exp IM.! var
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

cancelUsAtom :: (Fractional a, Eq a) => Atom a -> Atom a
cancelUsAtom (Atom k ds us exp) =
  case partitionEithers . map separate $ us of
    (ks, us) -> Atom (k * Prelude.product ks) ds us exp
    where
      separate (DiffSym (Variable _) (Constant 0)) = Left 1
      separate (DiffSym (Constant 0) (Variable _)) = Left 0
      separate u@(DiffSym x y) | x == y = Left (1 / 2)
                               | otherwise = Right u

groupifyAtoms :: (Eq a, Num a) => [Atom a] -> [Atom a]
groupifyAtoms [] = []
groupifyAtoms (a : as) = case partition (a `similar`) as of
  ([], rest) -> a : groupifyAtoms rest
  (found, rest) -> let Atom k0 ds us exp = a
                       a' = Atom (k0 + sum (map atomConstant found)) ds us exp
                   in a' : groupifyAtoms rest
  where
    similar (Atom _ ds1 us1 e1) (Atom _ ds2 us2 e2) =
      (e1 == e2) && (ds1 == ds2) && (us1 == us2)    
