import Control.Applicative

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (intersperse, nub, partition)
import Data.Maybe (fromJust)


data Expr a = ExprC (Term a) (Expr a)
            | ExprN (Term a)
            deriving (Show, Read, Eq)

data Term a = Term {
    termAtom :: Atom a
  , termExpr :: [Expr a]
  } deriving (Show, Read, Eq)

data Atom a = Atom a [Vector Int] [Vector Int] (Maybe (Vector a))
              deriving (Show, Read, Eq)

mapExpr :: (Term a -> Term a) -> Expr a -> Expr a
mapExpr f (ExprC t e) = ExprC (f t) (mapExpr f e)
mapExpr f (ExprN t) = ExprN (f t)

zipAlt :: Alternative f => (a -> a -> a) -> f a -> f a -> f a
zipAlt f a b = f <$> a <*> b <|> a <|> b

zeroAtom :: Num a => Atom a
zeroAtom = Atom 0 [] [] Nothing

oneAtom :: Num a => Atom a
oneAtom = Atom 1 [] [] Nothing

toList :: Expr a -> [Term a]
toList (ExprC t e) = t : toList e
toList (ExprN t) = [t]

fromList :: [Term a] -> Expr a
fromList (t : []) = ExprN t
fromList (t : ts) = ExprC t (fromList ts)
fromList [] = error "fromList: term list is empty"

texify :: (Show a, Num a, Ord a) => Expr a -> String
texify expr = let terms = texifyTerm <$> toList expr
                  signs = fst <$> terms
                  signStrs = (if head signs == '+' then "" else "-")
                             : [ ' ' : s : " " | s <- tail signs ]
              in concat $ zipWith (++) signStrs (snd <$> terms)

texifyTerm :: (Num a, Ord a, Show a) => Term a -> (Char, String)
texifyTerm (Term a es) = case texifyAtom a of
  (sign, atom) -> (sign, atom ++ delimiter ++ exprs)
    where
      delimiter = if null atom || null exprs then "" else " "
      exprs = concat . intersperse " " $ texifyAndParen <$> es
      texifyAndParen e@(ExprC _ _) = "\\left( " ++ texify e ++ " \\right)"
      texifyAndParen e@(ExprN _) = texify e

texifyAtom :: (Num a, Ord a, Show a) => Atom a -> (Char, String)
texifyAtom (Atom k deltas units exponent)
  | null deltas && null units && maybe False V.null exponent = (sign, show absK)
  | otherwise =
    (,) sign $
    (if absK == 1 then [] else show absK)
      ++ (concat . intersperse " " . map texifyDelta $ deltas)
      ++ (concat . intersperse " " . map texifyUnit $ units)
      ++ texifyExponent ((V.map negate) <$> exponent)
        where
          absK = abs k
          sign = if signum k == 1 then '+' else '-'
          texifyDelta d = "\\delta(" ++ texifyVarForm d ++ ")"
          texifyUnit u = "u(" ++ texifyVarForm u ++ ")"
          texifyExponent Nothing = []
          texifyExponent (Just e) = let vf = texifyVarForm e
                                    in if null vf then [] else "e^{" ++ vf ++ "}"

texifyVarForm :: (Show a, Num a, Ord a) => Vector a -> String
texifyVarForm = cutPlus . concat . zipWith texifyVar [1..] . V.toList
  where
    texifyVar n v | v == 0 = ""
                  | otherwise = sign v : (showNum v ++ "x_{" ++ show n ++ "}")
    sign v = if v > 0 then '+' else '-'
    showNum x = let ax = abs x in if ax == 1 then [] else show ax
    cutPlus ('+' : s) = s
    cutPlus s = s

normalizeDsUs :: Num a => Expr a -> Expr a
normalizeDsUs = mapExpr normalizeDsUsTerm

normalizeDsUsTerm :: Num a => Term a -> Term a
normalizeDsUsTerm (Term a es) = Term (normalizeDsUsAtom a) (normalizeDsUs <$> es)

normalizeDsUsAtom :: Num a => Atom a -> Atom a
normalizeDsUsAtom (Atom k ds us e) = Atom k (map swapDelta ds) (nub us) e
  where
    swapDelta d = if fromJust (V.find (/= 0) d) > 0 then d else V.map negate d

substitute :: (Num a, Eq a) => Int -> V.Vector Int -> Expr a -> Expr a
substitute v vec = mapExpr (substituteTerm v vec)

substituteTerm :: (Num a, Eq a) => Int -> V.Vector Int -> Term a -> Term a
substituteTerm v vec (Term a es) = Term (substituteAtom v vec a) (substitute v vec <$> es)

substituteAtom :: (Num a, Eq a) => Int -> V.Vector Int -> Atom a -> Atom a
substituteAtom v vec (Atom k ds us e) =
  Atom k (map (substituteForm v vec) ds) (map (substituteForm v vec) us)
  (fmap (substituteForm v . V.map fromIntegral $ vec) e)

substituteForm :: (Num a, Eq a) => Int -> Vector a -> Vector a -> Vector a
substituteForm v vec d | value == 0 = d
                       | otherwise = V.zipWith (+) (V.map (* value) vec) (d V.// [(v, 0)])
                         where value = d V.! v

deepExpand :: Num a => Expr a -> Expr a
deepExpand e | isExpandable e = deepExpand (expand e)
             | otherwise = e
  where
    isExpandable = any isExpandableTerm . toList
    isExpandableTerm (Term _ []) = False
    isExpandableTerm _ = True

expand :: Num a => Expr a -> Expr a
expand = fromList . concatMap (toList . expandTerm) . toList

expandTerm :: Num a => Term a -> Expr a
expandTerm (Term a []) = ExprN $ Term a []
expandTerm (Term a es) =
  fromList . map (foldl productTerm (Term a [])) . sequence $ toList <$> es

product :: Num a => Expr a -> Expr a -> Expr a
product e1 e2 = ExprN (Term oneAtom [e1, e2])

productTerm :: Num a => Term a -> Term a -> Term a
productTerm (Term a1 e1) (Term a2 e2) = Term (productAtom a1 a2) (e1 ++ e2)

productAtom :: Num a => Atom a -> Atom a -> Atom a
productAtom (Atom k1 d1 u1 e1) (Atom k2 d2 u2 e2) =
  normalizeDsUsAtom $ Atom (k1 * k2) (d1 ++ d2) (u1 ++ u2) (zipAlt (V.zipWith (+)) e1 e2)

distributionLambda :: Num a => Int -> Int -> a -> Expr a
distributionLambda length variable lambda =
  let exp = Just $ V.generate length (\i -> if i == variable then lambda else 0)
  in ExprN $ Term (Atom lambda [] [] exp) []

distributionAnd :: Num a => Int -> Int -> Int -> Int -> Expr a
distributionAnd length x a b =
  let zero = V.replicate length 0
      term p m i | i == p = 1
                 | i == m = -1
                 | otherwise = 0
      a1 = Atom 1 [V.generate length (term x b)] [V.generate length (term b a)] Nothing
      a2 = Atom 1 [V.generate length (term x a)] [V.generate length (term a b)] Nothing
  in ExprC (Term a1 []) (ExprN (Term a2 []))

simpleExpr :: Expr Int
simpleExpr = ExprN $ Term oneAtom [distributionAnd 3 2 0 1, distributionLambda 3 0 15, distributionLambda 3 1 35]

data Limit = Zero
           | Infinity
           | Limit (Vector Int)
           deriving (Eq, Read, Show)

integrate :: (Fractional a, Eq a) => Expr a -> Int -> Limit -> Limit -> Expr a
integrate expr var lo hi =
  let doTerm (Term a _) = integrateAtom a var lo hi
  in fromList . map (`Term` []) . concatMap doTerm . toList . deepExpand $ expr

integrateAtom :: (Fractional a, Eq a) => Atom a -> Int -> Limit -> Limit -> [Atom a]
integrateAtom (Atom k ds us (Just exp)) var lo hi =
  fromJust $ intEqualLimits <|> intDelta <|> intUnit <|> Just intExp
    where
      intEqualLimits | lo == hi = Just $ [Atom 0 [] [] Nothing]
                     | otherwise = Nothing
      
      intDelta = case partition (\d -> (d V.! var) /= 0) ds of
        ([], rest) -> Nothing
        (d : ds1, ds2) ->
          let vec = calcSubstitution d
              us1 = calcDeltaUnits vec
          in Just [substituteAtom var vec (Atom k (ds1 ++ ds2) (us1 ++ us) (Just exp))]

      calcSubstitution d | d V.! var > 0 = V.map negate (d V.// [(var, 0)])
                         | otherwise = d V.// [(var, 0)]

      calcDeltaUnits vec = lower lo : higher hi
        where
          lower Zero = vec
          lower Infinity = error "integrateAtom: lower infinite limit? wut?"
          lower (Limit l) = V.zipWith (-) vec l
          higher Zero = error "integrateAtom: higher zero limit? wut?"
          higher Infinity = []
          higher (Limit l) = [V.zipWith (-) l vec]

      intExp = let lambda = exp V.! var
                   subLimit a Infinity = zeroAtom
                   subLimit a Zero = substituteAtom var zeroVector a
                   subLimit a (Limit l) = substituteAtom var l a
               in [ subLimit (Atom (-k / lambda) ds us (Just exp)) hi
                  , subLimit (Atom (k / lambda) ds us (Just exp)) lo
                  ]
      
      zeroVector = V.replicate (V.length exp) 0

      intUnit = intUnit' <$> findUnit
      intUnit' (u, us) | (u V.! var) > 0 =
        let vec = V.map negate (u V.// [(var, 0)])
        in case hi of
          Infinity ->
            let u1 = V.zipWith (-) lowerLimit vec
            in integrateAtom (Atom k ds us (Just exp)) var (Limit vec) Infinity
               ++ integrateAtom (Atom k ds (u1 : us) (Just exp)) var lo (Limit vec)
          Limit higherLimit ->
            let u1 = V.zipWith (-) higherLimit vec
                u2 = V.zipWith (-) vec lowerLimit
                u3 = V.zipWith (-) lowerLimit vec
            in integrateAtom (Atom k ds (u1 : u2 : us) (Just exp)) var (Limit vec) hi
               ++ integrateAtom (Atom k ds (u3 : us) (Just exp)) var lo hi
          Zero -> error "integrateAtom: zero at higher limit? no wai"
                       | otherwise =
        let vec = u V.// [(var, 0)]
        in case hi of
          Infinity ->
            let u1 = V.zipWith (-) vec lowerLimit
            in integrateAtom (Atom k ds (u1 : us) (Just exp)) var lo (Limit vec)
          Limit higherLimit ->
            let u1 = V.zipWith (-) vec lowerLimit
                u2 = V.zipWith (-) higherLimit vec
                u3 = V.zipWith (-) vec higherLimit
            in integrateAtom (Atom k ds (u1 : u2 : us) (Just exp)) var lo (Limit vec)
               ++ integrateAtom (Atom k ds (u3 : us) (Just exp)) var lo hi
          Zero -> error "integrateAtom: zero at higher limit? no wai"
      
      findUnit = case partition (\u -> (u V.! var) /= 0) us of
        ([], rest) -> Nothing
        (u : us1, us2) -> Just (u, us1 ++ us2)
        
      lowerLimit = case lo of
        Infinity -> error "integrateAtom: infinity at lower limit? wut?"
        Limit l -> l
        Zero -> zeroVector

--main :: IO ()
--main = putStrLn . (\t -> "$$ " ++ t ++ " $$") . texify . deepExpand $ simpleExpr
