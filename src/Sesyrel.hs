{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

import Sesyrel.FaultTree
import Sesyrel.Distribution
import Sesyrel.Expression (evalExpr, mapExprType, texifyDoubleE)

import Control.Monad.Writer

import Prelude hiding (Rational)

import qualified Data.Text.Lazy.Builder as TB
import qualified Data.Text.Lazy.IO as T

import qualified Data.IntMap as IM (singleton)


main :: IO ()
main = do
  let doIt (name, mbOrder, ftreeM, points) =
        let (vars, FaultTreeSesyrel _ factors) = evalFaultTreeSesyrelM ftreeM
            doIntegral = case mbOrder of
              Nothing -> factorsSimpleProcess name (Left vars) factors
              Just vs -> factorsSimpleProcess name (Right vs) factors
            texifyPoint p v =
              tell
              ("\\\\  $ F(" <> texifyDoubleE 3 p <> ") = " <> texifyDoubleE 3 v <> " $\n")
        in do
          (_, mbExpr) <- doIntegral
          case mbExpr of
            Nothing -> return ()
            Just expr -> do
              let expr' = mapExprType fromRational expr
              tell "Evaluation of some points in distribution:\n"
              forM_ points $ \p ->
                texifyPoint p (evalExpr expr' (IM.singleton 0 p))
              tell "\n"
  T.writeFile "output.tex" . TB.toLazyText . execWriter . mapM_ doIt $ trees

trees :: [(String, Maybe [Int], FaultTreeSesyrelM [Int], [Double])]
trees =
  [-- ("ftree1", Nothing, simpleFaultTreeSesyrelM, [1, 3])
  --, ("ftree1", Just [4, 1, 3, 2], simpleFaultTreeSesyrelM, [])
  ("traditional", Nothing, traditionalHydrosystemsM True >>= traditionalActuationsM True, [5e-6])
  -- ("more electrical", Nothing, medianHydrosystemsM True >>= medianActuationsM True, [5e-6])
  -- ("electrical", Nothing, electroHydrosystemsM True False >>= electroActuationsM False, [5e-6])
  ]

testTreeM :: FaultTreeSesyrelM [Int]
testTreeM = do
  a <- lambdaM 3.0
  b <- lambdaM 5.0
  c <- orM b b
  d <- orM b c
  _ <- andM a c
  _ <- andM c d
  return []

simpleFaultTreeSesyrelM :: FaultTreeSesyrelM [Int]
simpleFaultTreeSesyrelM = do
  a <- lambdaM 15.0
  b <- lambdaM 35.0
  _ <- andM a b
  c <- lambdaM 3.0
  t <- andM a c
  return [t]

escalatorChannelM :: Int -> FaultTreeSesyrelM Int
escalatorChannelM hydro = do
  ccu <- lambdaM 50
  steer <- lambdaM 15
  x <- orM ccu hydro
  orM x steer

escalatorFaultTreeSesyrel1 :: FaultTreeSesyrelM [Int]
escalatorFaultTreeSesyrel1 = do
  let escalatorSectionM h1 h2 = do
        c1 <- escalatorChannelM h1
        c2 <- escalatorChannelM h2
        valve <- lambdaM 10
        cAndC <- andM c1 c2
        priorityAndOrM valve c1 cAndC
  hydro1 <- lambdaM 70
  hydro2 <- lambdaM 70
  hydro3 <- lambdaM 70
  section1 <- escalatorSectionM hydro1 hydro2
  section2 <- escalatorSectionM hydro1 hydro3
  t <- andM section1 section2
  return [t]

escalatorFaultTreeSesyrel2 :: FaultTreeSesyrelM [Int]
escalatorFaultTreeSesyrel2 = do
  let escalatorSectionM h1 h2 = do
        c1 <- escalatorChannelM h1
        c2 <- escalatorChannelM h2
        valve <- lambdaM 10
        x <- orM c2 valve
        andM c1 x
  hydro1 <- lambdaM 70
  hydro2 <- lambdaM 70
  hydro3 <- lambdaM 70
  section1 <- escalatorSectionM hydro1 hydro2
  section2 <- escalatorSectionM hydro1 hydro3
  t <- andM section1 section2
  return [t]

traditionalHydrosystemsM :: Bool -> FaultTreeSesyrelM [Int]
traditionalHydrosystemsM doValves = do
  [engineL, engineR] <- replicateM 2 (lambdaM 82)
  [electroGrpL, electroGrpR] <- replicateM 2 (lambdaM 60)
  [tank1, tank2, tank3] <- replicateM 3 (lambdaM 3)
  [hydroPump1, hydroPump2, hydroPump3] <- replicateM 3 (lambdaM 12.5)
  [electromotor1, electromotor2, electromotor3] <- replicateM 3 (lambdaM 10)
  [pumpStation1, pumpStation2, pumpStation3] <- replicateM 3 (lambdaM 56.7)
  [valve1, valve2, valve3] <- replicateM 3 (lambdaM 5.8)
  
  electroSysL <- orM engineL electroGrpL
  electroSysR <- orM engineL electroGrpR
  electroSys <- andM electroSysL electroSysR
  
  hydro2Main <- orM electromotor2 pumpStation2 >>= orM electroSys
  let hydro2Res = hydroPump2
      swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  hydro2 <- swM valve2 hydro2Main hydro2Res >>= orM tank2
  
  hydro1Main <- orM hydroPump1 engineL
  hydro3Main <- orM hydroPump3 engineR
  hydro1Res <- orM pumpStation1 electromotor1 >>= orM electroSys
  hydro3Res <- orM pumpStation3 electromotor3 >>= orM electroSys
  hydro1 <- swM valve1 hydro1Main hydro1Res >>= orM tank1
  hydro3 <- swM valve3 hydro3Main hydro3Res >>= orM tank3
  return [hydro1, hydro2, hydro3]

traditionalActuationsM :: Bool -> [Int] -> FaultTreeSesyrelM [Int]
traditionalActuationsM doValves [hydro1, hydro2, hydro3] = do
  [ccu1, ccu2, ccu3, ccu4] <- replicateM 4 (lambdaM 22)
  [steer1, steer2, steer3, steer4] <- replicateM 4 (lambdaM 40)
  [valve1, valve2] <- replicateM 2 (lambdaM 20)
  let swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  channel1 <- orM hydro1 ccu1 >>= orM steer1
  channel2 <- orM hydro2 ccu2 >>= orM steer2
  channel3 <- orM hydro2 ccu3 >>= orM steer3
  channel4 <- orM hydro3 ccu4 >>= orM steer4
  elevator1 <- swM valve1 channel1 channel2
  elevator2 <- swM valve2 channel3 channel4
  elevator <- andM elevator1 elevator2
  return [elevator]

medianHydrosystemsM :: Bool -> FaultTreeSesyrelM [Int]
medianHydrosystemsM doValves = do
  [engineL, engineR] <- replicateM 2 (lambdaM 82)
  [electroGrpL, electroGrpR] <- replicateM 2 (lambdaM 60)
  [tank1, tank2] <- replicateM 2 (lambdaM 3)
  [hydroPump1, hydroPump2] <- replicateM 2 (lambdaM 12.5)
  [electromotor1, electromotor2] <- replicateM 2 (lambdaM 10)
  [pumpStation1, pumpStation2] <- replicateM 2 (lambdaM 56.7)
  [valve1, valve2] <- replicateM 2 (lambdaM 5.8)
  
  electroSysL <- orM engineL electroGrpL
  electroSysR <- orM engineL electroGrpR
  electroSys <- andM electroSysL electroSysR

  let swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  hydro1Main <- orM hydroPump1 engineL
  hydro2Main <- orM hydroPump2 engineR
  hydro1Res <- orM pumpStation1 electromotor1 >>= orM electroSys
  hydro2Res <- orM pumpStation2 electromotor2 >>= orM electroSys
  hydro1 <- swM valve1 hydro1Main hydro1Res >>= orM tank1
  hydro2 <- swM valve2 hydro2Main hydro2Res >>= orM tank2
  return [hydro1, hydro2, electroSys]

medianActuationsM :: Bool -> [Int] -> FaultTreeSesyrelM [Int]
medianActuationsM doValves [hydro1, hydro2, electroSys] = do
  [ccu1, ccu2, ccuE1, ccuE2] <- replicateM 4 (lambdaM 22)
  [steer1, steer2] <- replicateM 2 (lambdaM 40)
  [steerE1, steerE2] <- replicateM 2 (lambdaM 115)
  [valve1, valve2] <- replicateM 2 (lambdaM 20)
  let swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  channel1 <- orM hydro1 ccu1 >>= orM steer1
  channel2 <- orM electroSys ccuE1 >>= orM steerE1
  channel3 <- orM hydro2 ccu2 >>= orM steer2
  channel4 <- orM electroSys ccuE2 >>= orM steerE2
  elevator1 <- swM valve1 channel1 channel2
  elevator2 <- swM valve2 channel3 channel4
  elevator <- andM elevator1 elevator2
  return [elevator]

electroHydrosystemsM :: Bool -> Bool -> FaultTreeSesyrelM [Int]
electroHydrosystemsM withAccum doValves = do
  [engineL, engineR] <- replicateM 2 (lambdaM 82)
  [electroGrpL, electroGrpR] <- replicateM 2 (lambdaM 60)
  [electromotor1, electromotor2] <- replicateM 2 (lambdaM 10)
  [valve1, valve2] <- replicateM 2 (lambdaM 5.8)
  
  electroSysL <- orM engineL electroGrpL
  electroSysR <- orM engineR electroGrpR
  electroSys <- andM electroSysL electroSysR

  let swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  let electroSysRes1 = electromotor1
  electroSys1 <- swM valve1 electroSys electroSysRes1
  
  electroSys2 <- case withAccum of
    True -> do
      accumulator <- lambdaM 0.05
      swM valve2 electroSys accumulator
    False -> do
      return electroSys
  
  return [electroSys1, electroSys2]

electroActuationsM :: Bool -> [Int] -> FaultTreeSesyrelM [Int]
electroActuationsM doValves [esys1, esys2] = do
  [ccu1, ccu2, ccu3, ccu4] <- replicateM 4 (lambdaM 22)
  [steer1, steer2, steer3, steer4] <- replicateM 4 (lambdaM 100)
  [valve1, valve2] <- replicateM 2 (lambdaM 20)
  let swM v a b = if doValves then switchM v a b else orM v b >>= andM a
  channel1 <- orM esys1 ccu1 >>= orM steer1
  channel2 <- orM esys2 ccu2 >>= orM steer2
  channel3 <- orM esys2 ccu3 >>= orM steer3
  channel4 <- orM esys1 ccu4 >>= orM steer4
  elevator1 <- swM valve1 channel1 channel2
  elevator2 <- swM valve2 channel3 channel4
  elevator <- andM elevator1 elevator2
  return [elevator]
