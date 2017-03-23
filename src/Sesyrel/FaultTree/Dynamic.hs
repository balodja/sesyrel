module Sesyrel.FaultTree.Dynamic (
  compileDynamicFaultTree
  ) where

import Sesyrel.FaultTree.Base
import Sesyrel.Distribution

compileDynamicFaultTree :: FaultTree Rational -> [Factor]
compileDynamicFaultTree (FaultTree ft) = map reNode ft
  where
    reNode :: (Int, FaultTreeNode Rational) -> Factor
    reNode (x, FaultTreeLambda k) = (distributionLambda x k, [x])
    reNode (x, FaultTreeAnd a b) = (distributionAnd x a b, [x, a, b])
    reNode (x, FaultTreeOr a b) = (distributionOr x a b, [x, a, b])
    reNode (x, FaultTreePriorityAndOr a b c) = (distributionPriorityAndOr x a b c, [x, a, b, c])
    reNode (x, FaultTreeSwitch s a b) = (distributionSwitch x s a b, [x, s, a, b])
