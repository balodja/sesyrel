import Control.Applicative

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (intersperse, nub, partition)
import Data.Maybe (fromJust, maybe)

data Expr a = AddE (Expr a) (Expr a)
            | MulE (Expr a) (Expr a)
            | AtomE a [Vector Int] [Vector Int] (Maybe (Vector a))
            | IntE (Expr a) Int (Limit, Limit)
            deriving (Eq, Read, Show)

data Limit = Zero
           | Infinity
           | Limit (Vector Int)
           deriving (Eq, Read, Show)


-- some magic
zipAlt :: Alternative f => (a -> a -> a) -> f a -> f a -> f a
zipAlt f a b = f <$> a <*> b <|> a <|> b

texify :: (Show a, Num a, Ord a) => Expr a -> String
texify (AddE e1 e2) = texify e1 ++ " + " ++ texify e2
texify (MulE e1 e2) = texifyMul e1 ++ " " ++ texifyMul e2
  where
    texifyMul e@(AddE _ _) = "\\left( " ++ texify e ++ " \\right)"
    texifyMul e = texify e
texify (AtomE k deltas units exponent)
  | null deltas && null units && maybe False V.null exponent = show k
  | otherwise =
    (if k == 1 then [] else show k)
      ++ (concat . intersperse " " . map texifyDelta $ deltas)
      ++ (concat . intersperse " " . map texifyUnit $ units)
      ++ texifyExponent (fmap (V.map negate) exponent)
        where
          texifyDelta d = "\\delta(" ++ texifyVarForm d ++ ")"
          texifyUnit u = "u(" ++ texifyVarForm u ++ ")"
          texifyExponent Nothing = []
          texifyExponent (Just e) = let vf = texifyVarForm e
                                    in if null vf then [] else "e^{" ++ vf ++ "}"
texify (IntE e v (l1, l2)) =
  "\\int\\limits_" ++ texifyLimit l1 ++ "^" ++ texifyLimit l2 ++ " "
  ++ texify e ++ " \\textrm{dx}_{" ++ show (v + 1) ++ "}"
    where
      texifyLimit Infinity = "{+\\infty}"
      texifyLimit Zero = "0"
      texifyLimit (Limit x) = "{" ++ texifyVarForm x ++ "}"

texifyVarForm :: (Show a, Num a, Ord a) => Vector a -> String
texifyVarForm = cutPlus . concat . zipWith texifyVar [1..] . V.toList
  where
    texifyVar n v | v == 0 = ""
                  | otherwise = sign v : (showNum v ++ "x_{" ++ show n ++ "}")
    sign v = if v > 0 then '+' else '-'
    showNum x = let ax = abs x in if ax == 1 then [] else show ax
    cutPlus ('+' : s) = s
    cutPlus s = s

normalizeLists :: Expr a -> Expr a
normalizeLists (MulE e1@(MulE _ _) e2) =
  case normalizeLists e1 of
    MulE e11 e12 -> normalizeLists (MulE e11 (MulE e12 e2))
    _ -> error "normalizeLists: strange error"
normalizeLists (AddE e1@(AddE _ _) e2) =
  case normalizeLists e1 of
    AddE e11 e12 -> normalizeLists (AddE e11 (AddE e12 e2))
    _ -> error "normalizeLists: strange error"
normalizeLists (IntE e v l) = IntE (normalizeLists e) v l
normalizeLists e = e

normalizeOrder :: Expr a -> Expr a
normalizeOrder (MulE e1@(AddE _ _) e2@(AtomE _ _ _ _)) = MulE e2 e1
normalizeOrder (MulE e1@(AddE _ _) (MulE e2@(AtomE _ _ _ _) e3)) =
  MulE e2 (normalizeOrder (MulE e1 e3))
normalizeOrder (MulE e1@(IntE _ _ _) e2@(AtomE _ _ _ _)) = MulE e2 e1
normalizeOrder (MulE e1@(IntE _ _ _) (MulE e2@(AtomE _ _ _ _) e3)) =
  MulE e2 (normalizeOrder (MulE e1 e3))
normalizeOrder (MulE e1@(IntE _ _ _) e2@(AddE _ _)) = MulE e2 e1
normalizeOrder (MulE e1@(IntE _ _ _) (MulE e2@(AddE _ _) e3)) =
  MulE e2 (normalizeOrder (MulE e1 e3))
normalizeOrder (AddE e1@(MulE _ _) e2@(AtomE _ _ _ _)) = AddE e2 e1
normalizeOrder (AddE e1@(MulE _ _) (AddE e2@(AtomE _ _ _ _) e3)) =
  AddE e2 (normalizeOrder (AddE e1 e3))
normalizeOrder (AddE e1@(IntE _ _ _) e2@(AtomE _ _ _ _)) = AddE e2 e1
normalizeOrder (AddE e1@(IntE _ _ _) (AddE e2@(AtomE _ _ _ _) e3)) =
  AddE e2 (normalizeOrder (AddE e1 e3))
normalizeOrder (AddE e1@(IntE _ _ _) e2@(MulE _ _)) = AddE e2 e1
normalizeOrder (AddE e1@(IntE _ _ _) (AddE e2@(MulE _ _) e3)) =
  AddE e2 (normalizeOrder (AddE e1 e3))
normalizeOrder (IntE e v l) = IntE (normalizeOrder e) v l
normalizeOrder e = e

normalizeDsAndUs :: Num a => Expr a -> Expr a
normalizeDsAndUs (MulE e1 e2) = MulE (normalizeDsAndUs e1) (normalizeDsAndUs e2)
normalizeDsAndUs (AddE e1 e2) = AddE (normalizeDsAndUs e1) (normalizeDsAndUs e2)
normalizeDsAndUs (IntE e v l) = IntE (normalizeDsAndUs e) v l
normalizeDsAndUs (AtomE k ds us e) = AtomE k (map swapDelta ds) (nub us) e
  where
    swapDelta d = if fromJust (V.find (/= 0) d) > 0 then d else V.map negate d

normalize :: Num a => Expr a -> Expr a
normalize = normalizeOrder . normalizeLists . normalizeDsAndUs

groupify :: Num a => Expr a -> Expr a
groupify = groupifyMulAtoms

groupifyMulAtoms :: Num a => Expr a -> Expr a
groupifyMulAtoms e@(AtomE _ _ _ _) = e
groupifyMulAtoms (MulE (AtomE k1 d1 u1 e1) (AtomE k2 d2 u2 e2)) =
  AtomE (k1 * k2) (d1 ++ d2) (u1 ++ u2) (zipAlt (V.zipWith (+)) e1 e2)
groupifyMulAtoms (MulE (AtomE k1 d1 u1 e1) (MulE (AtomE k2 d2 u2 e2) e)) =
  groupifyMulAtoms $
  MulE (AtomE (k1 * k2) (d1 ++ d2) (u1 ++ u2) (zipAlt (V.zipWith (+)) e1 e2)) e
groupifyMulAtoms (MulE e1@(AtomE _ _ _ _) e2) = MulE e1 (groupifyMulAtoms e2)
groupifyMulAtoms (MulE e1 e2) = MulE (groupifyMulAtoms e1) (groupifyMulAtoms e2)
groupifyMulAtoms (AddE e1 e2) = AddE (groupifyMulAtoms e1) (groupifyMulAtoms e2)
groupifyMulAtoms (IntE e v l) = IntE (groupifyMulAtoms e) v l

substitute :: (Num a, Eq a) => Int -> V.Vector Int -> Expr a -> Expr a
substitute v vec (MulE e1 e2) = MulE (substitute v vec e1) (substitute v vec e2)
substitute v vec (AddE e1 e2) = AddE (substitute v vec e1) (substitute v vec e2)
substitute v vec (IntE _ _ _) = error "substitute: integral? that should not happen"
substitute v vec (AtomE k ds us e) =
  AtomE k (map (substituteForm v vec) ds) (map (substituteForm v vec) us)
  (fmap (substituteForm v . V.map fromIntegral $ vec) e)

substituteForm :: (Num a, Eq a) => Int -> Vector a -> Vector a -> Vector a
substituteForm v vec d | value == 0 = d
                       | otherwise = V.zipWith (+) (V.map (* value) vec) (d V.// [(v, 0)])
                         where value = d V.! v

integrateStep :: (Num a, Eq a) => Expr a -> (Bool, Expr a)
integrateStep (MulE e1 e2) = let (b1, e1') = integrateStep e1
                                 (b2, e2') = integrateStep e2
                             in (b1 || b2, MulE e1' e2')
integrateStep (AddE e1 e2) = let (b1, e1') = integrateStep e1
                                 (b2, e2') = integrateStep e2
                             in (b1 || b2, AddE e1' e2')
integrateStep e@(AtomE _ _ _ _) = (False, e)
integrateStep (IntE e v ls) = (True, integrate' e v ls)

integrate' :: (Num a, Eq a) => Expr a -> Int -> (Limit, Limit) -> Expr a
integrate' expr var ls = fromJust $ intEqualLimits <|> intDelta <|> intUnit <|> intAdd <|> intMul <|> Just intExp
  where
    intEqualLimits | fst ls == snd ls = Just $ AtomE 0 [] [] Nothing
                   | otherwise = Nothing
    
    intDelta = (\(d, expr) -> let vec = calcSubstitution d
                              in MulE (calcLimitUnits var vec ls) (substitute var vec expr))
               <$> intFindDelta expr
    
    intFindDelta (AtomE k ds us e) = case partition (\d -> (d V.! var) /= 0) ds of
      ([], rest) -> Nothing
      (d : ds1, ds2) -> Just (d, AtomE k (ds1 ++ ds2) us e)
    intFindDelta (AddE _ _) = Nothing
    intFindDelta (MulE e1 e2) =
      case intFindDelta e1 of
        Just (vec, e) -> Just (vec, MulE e e2)
        Nothing -> case intFindDelta e2 of
          Just (vec, e) -> Just (vec, MulE e1 e)
          Nothing -> Nothing
    intFindDelta (IntE _ _ _) = error "intFindDelta: integral? that should not happen"
    
    intUnit = intUnit' (snd ls) <$> intFindUnit expr
    intUnit' (Limit higherLimit) (u, expr) | (u V.! var) > 0 = 
      let vec = V.map negate (u V.// [(var, 0)])
          lowerLimit = truncateLowerLimit (V.length u) (fst ls)
      in AddE
         (MulE
          (AtomE 1 [] [V.zipWith (-) higherLimit vec, V.zipWith (-) vec lowerLimit] Nothing)
          (IntE expr var (Limit vec, Limit higherLimit)))
         (MulE
          (AtomE 1 [] [V.zipWith (-) lowerLimit vec] Nothing)
          (IntE expr var ls))
                       | otherwise =
      let vec = u V.// [(var, 0)]
          lowerLimit = truncateLowerLimit (V.length u) (fst ls)
      in AddE
         (MulE
          (AtomE 1 [] [V.zipWith (-) vec lowerLimit, V.zipWith (-) higherLimit vec] Nothing)
          (IntE expr var (fst ls, Limit vec)))
         (MulE
          (AtomE 1 [] [V.zipWith (-) vec higherLimit] Nothing)
          (IntE expr var ls))
    intUnit' Infinity (u, expr) | (u V.! var) > 0 =
      let vec = V.map negate (u V.// [(var, 0)])
          lowerLimit = truncateLowerLimit (V.length u) (fst ls)
      in AddE
         (IntE expr var (Limit vec, Infinity))
         (MulE
          (AtomE 1 [] [V.zipWith (-) lowerLimit vec] Nothing)
          (IntE expr var (fst ls, Limit vec)))
                                | otherwise =
      let vec = u V.// [(var, 0)]
          lowerLimit = truncateLowerLimit (V.length u) (fst ls)
      in MulE
         (AtomE 1 [] [V.zipWith (-) vec lowerLimit] Nothing)
         (IntE expr var (fst ls, Limit vec))
    intUnit' Zero _ = error "intUnit': zero at higher limit? no-no-no"
    
    intFindUnit (AtomE k ds us e) = case partition (\u -> (u V.! var) /= 0) us of
      ([], rest) -> Nothing
      (u : us1, us2) -> Just (u, AtomE k ds (us1 ++ us2) e)
    intFindUnit (AddE _ _) = Nothing
    intFindUnit (MulE e1 e2) =
      case intFindUnit e1 of
        Just (vec, e) -> Just (vec, MulE e e2)
        Nothing -> case intFindUnit e2 of
          Just (vec, e) -> Just (vec, MulE e1 e)
          Nothing -> Nothing
    intFindUnit (IntE _ _ _) = error "intFindUnit: integral? that should not happen"
    
    intExp = undefined
    intAdd = undefined
    intMul = undefined
    
    calcSubstitution d | d V.! var > 0 = V.map negate (d V.// [(var, 0)])
                       | otherwise = d V.// [(var, 0)]
    
    calcLimitUnits :: (Num a, Eq a) => Int -> V.Vector Int -> (Limit, Limit) -> Expr a
    calcLimitUnits var vec (l1, l2) = AtomE 1 [] (lower l1 : higher l2) Nothing
      where
        lower Zero = vec
        lower Infinity = error "calcLimitUnits: lower infinite limit? wut?"
        lower (Limit d) = V.zipWith (-) vec d
        higher Zero = error "calcLimitUnits: higher zero limit? wut?"
        higher Infinity = []
        higher (Limit d) = [V.zipWith (-) d vec]
    
    truncateLowerLimit :: Int -> Limit -> V.Vector Int
    truncateLowerLimit n Infinity = error "truncateLowerLimit: infinity? no wai"
    truncateLowerLimit n Zero = V.replicate n 0
    truncateLowerLimit n (Limit v) = v

distributionLambda :: Num a => Int -> Int -> a -> Expr a
distributionLambda length variable lambda =
  AtomE lambda [] [] (Just $ V.generate length (\i -> if i == variable then lambda else 0))

distributionAnd :: Num a => Int -> Int -> Int -> Int -> Expr a
distributionAnd length x a b =
  AddE
  (AtomE 1 [V.generate length (term x b)] [V.generate length (term b a)] Nothing)
  (AtomE 1 [V.generate length (term x a)] [V.generate length (term a b)] Nothing)
    where
      zero = V.replicate length 0
      term p m i | i == p = 1
                 | i == m = -1
                 | otherwise = 0

simpleExpr :: Expr Int
simpleExpr = MulE (MulE (distributionAnd 3 2 0 1) (distributionLambda 3 0 15)) (distributionLambda 3 1 35)

main = putStrLn ("$$ " ++ texify simpleExpr ++ " $$\n\n$$" ++ (texify . groupify . normalize $ simpleExpr) ++ "$$")