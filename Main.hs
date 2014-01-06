
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.List (intersperse)

data Expr a = Add (Expr a) (Expr a)
            | Mul (Expr a) (Expr a)
            | Atom a [Vector Int] [Vector Int] (Vector a)
            | Integral (Expr a) Int (Limit a, Limit a)
              deriving (Eq, Read, Show)

data Limit a = Zero | Infinity | Limit a
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
          texifyVarForm :: (Show a, Num a, Ord a) => Vector a -> String
          texifyVarForm = cutPlus . concat . zipWith texifyVar [1..] . V.toList
          texifyVar n v | v == 0 = ""
                        | otherwise = sign v : (showNum v ++ "x_{" ++ show n ++ "}")
          sign v = if v > 0 then '+' else '-'
          showNum x = let ax = abs x in if ax == 1 then [] else show ax
          cutPlus ('+' : s) = s
          cutPlus s = s
texify (Integral e v (l1, l2)) =
  "\\int\\limits_" ++ texifyLimit l1 ++ "^" ++ texifyLimit l2 ++ " "
  ++ texify e ++ " \\textrm{dx}_{" ++ show (v + 1) ++ "}"
    where
      texifyLimit Infinity = "+\\infty"
      texifyLimit Zero = "0"
      texifyLimit (Limit x) = show x

simpleExpr :: Expr Int
simpleExpr =
  Mul
  (Add
   (Atom 1 [V.fromList [1, 0, -1]] [V.fromList [-1, 1, 0]] (V.fromList [0, 0, 3]))
   (Atom 3 [] [V.fromList [0, 1, -1]] (V.fromList [1, 0, 2])))
  (Atom 1 [] [] (V.fromList [1, 0, 0]))

main = putStrLn ("$$ " ++ texify simpleExpr ++ " $$")