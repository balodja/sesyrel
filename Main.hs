
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (intersperse)

data Expr a = Add (Expr a) (Expr a)
            | Mul (Expr a) (Expr a)
            | Atom a [Vector Int] [Vector Int] (Vector a)
            | Integral (Expr a) Int (Limit a, Limit a)
            deriving (Eq, Read, Show)

data Limit a = Zero
             | Infinity
             | Limit (Vector a)
             deriving (Eq, Read, Show)

texify :: (Show a, Num a, Ord a) => Expr a -> String
texify (Add e1 e2) = texify e1 ++ " + " ++ texify e2
texify (Mul e1 e2) = texifyMul e1 ++ " " ++ texifyMul e2
  where
    texifyMul e@(Add _ _) = "\\left( " ++ texify e ++ " \\right)"
    texifyMul e = texify e
texify (Atom k deltas units exponent)
  | null deltas && null units && V.null exponent = show k
  | otherwise =
    (if k == 1 then [] else show k)
      ++ (concat . intersperse " " . map texifyDelta $ deltas)
      ++ (concat . intersperse " " . map texifyUnit $ units)
      ++ texifyExponent (V.map negate exponent)
        where
          texifyDelta d = "\\delta(" ++ texifyVarForm d ++ ")"
          texifyUnit u = "u(" ++ texifyVarForm u ++ ")"
          texifyExponent e = "e^{" ++ texifyVarForm e ++ "}"
texify (Integral e v (l1, l2)) =
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
normalizeLists (Mul e1@(Mul _ _) e2) =
  case normalizeLists e1 of
    Mul e11 e12 -> normalizeLists (Mul e11 (Mul e12 e2))
    _ -> error "normalizeLists: strange error"
normalizeLists (Add e1@(Add _ _) e2) =
  case normalizeLists e1 of
    Add e11 e12 -> normalizeLists (Add e11 (Add e12 e2))
    _ -> error "normalizeLists: strange error"
normalizeLists (Integral e v l) = Integral (normalizeLists e) v l
normalizeLists e = e

normalizeOrder :: Expr a -> Expr a
normalizeOrder (Mul e1@(Add _ _) e2@(Atom _ _ _ _)) = Mul e2 e1
normalizeOrder (Mul e1@(Add _ _) (Mul e2@(Atom _ _ _ _) e3)) =
  Mul e2 (normalizeOrder (Mul e1 e3))
normalizeOrder (Mul e1@(Integral _ _ _) e2@(Atom _ _ _ _)) = Mul e2 e1
normalizeOrder (Mul e1@(Integral _ _ _) (Mul e2@(Atom _ _ _ _) e3)) =
  Mul e2 (normalizeOrder (Mul e1 e3))
normalizeOrder (Mul e1@(Integral _ _ _) e2@(Add _ _)) = Mul e2 e1
normalizeOrder (Mul e1@(Integral _ _ _) (Mul e2@(Add _ _) e3)) =
  Mul e2 (normalizeOrder (Mul e1 e3))
normalizeOrder (Add e1@(Mul _ _) e2@(Atom _ _ _ _)) = Add e2 e1
normalizeOrder (Add e1@(Mul _ _) (Add e2@(Atom _ _ _ _) e3)) =
  Add e2 (normalizeOrder (Add e1 e3))
normalizeOrder (Add e1@(Integral _ _ _) e2@(Atom _ _ _ _)) = Add e2 e1
normalizeOrder (Add e1@(Integral _ _ _) (Add e2@(Atom _ _ _ _) e3)) =
  Add e2 (normalizeOrder (Add e1 e3))
normalizeOrder (Add e1@(Integral _ _ _) e2@(Mul _ _)) = Add e2 e1
normalizeOrder (Add e1@(Integral _ _ _) (Add e2@(Mul _ _) e3)) =
  Add e2 (normalizeOrder (Add e1 e3))
normalizeOrder (Integral e v l) = Integral (normalizeOrder e) v l
normalizeOrder e = e

normalize :: Expr a -> Expr a
normalize = normalizeOrder . normalizeLists

simpleExpr :: Expr Int
simpleExpr = Integral integrant 1 (Limit (V.fromList [1, 0, 0]), Infinity)
  where
    integrant = 
      Mul
      (Add
       (Atom 1 [V.fromList [1, 0, -1]] [V.fromList [-1, 1, 0]] (V.fromList [0, 0, 3]))
       (Atom 3 [] [V.fromList [0, 1, -1]] (V.fromList [1, 0, 2])))
      (Atom 1 [] [] (V.fromList [1, 0, 0]))

main = putStrLn ("$$ " ++ texify simpleExpr ++ " $$\n\n$$" ++ texify (normalize simpleExpr) ++ "$$")