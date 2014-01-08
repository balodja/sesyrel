import Expression

import qualified Data.Set as Set

simpleExpr :: Expr Double
simpleExpr = ExprN $ Term
             (Atom 1 Set.empty Set.empty Nothing)
             [ distributionAnd 3 2 0 1
             , distributionLambda 3 0 15
             , distributionLambda 3 1 35
             ]

main :: IO ()
main = putStrLn . (\t -> "$$ " ++ t ++ " $$") . texify $ integrate (integrate simpleExpr 0 Zero Infinity) 1 Zero Infinity
