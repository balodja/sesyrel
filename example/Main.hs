{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

import Sesyrel.FaultTree
import Sesyrel.FaultTree.Dynamic

import Control.Monad (replicateM, forM_)
import Control.Monad.Logger
import System.Log.FastLogger

main :: IO ()
main = withFastLogger (LogFileNoRotate "output.tex" 1048576) $ \logger ->
  runLoggingT (mainS >> mainD) (\_ _ _ -> logger)

processDynamicFaultTree :: MonadLogger m => String -> Maybe [Variable] -> FaultTreeMonad Rational [Variable] -> m [DynamicFactor]
processDynamicFaultTree name mbOrder ftreeM =
  let (vars, ftree) = runFaultTreeMonad ftreeM
      factors = compileDynamicFaultTree ftree
  in factorsSimpleProcess name (maybe (Left vars) Right mbOrder) factors

processStaticFaultTree :: MonadLogger m => String -> Maybe [Variable] -> FaultTreeMonad Double [Variable] -> [Double] -> m ()
processStaticFaultTree name mbOrder ftreeM points =
  let (vars, ftree) = runFaultTreeMonad ftreeM
  in forM_ points $ \p ->
    let factors = compileStaticFaultTree ftree p
    in factorsSimpleProcess (name ++ " at " ++ show p) (maybe (Left vars) Right mbOrder) factors

mainD :: MonadLogger m => m ()
mainD =
  let doIt (name, mbOrder, ftreeM, points) = do
        factor : _ <- processDynamicFaultTree name mbOrder ftreeM
        logDynamicFactorInfo factor points
  in mapM_ doIt treesD

mainS :: MonadLogger m => m ()
mainS =
  let doIt (name, mbOrder, ftreeM, points) =
        processStaticFaultTree name mbOrder ftreeM points
  in mapM_ doIt treesS

treesD :: Fractional k => [(String, Maybe [Variable], FaultTreeMonad k [Variable], [Double])]
treesD =
  [ ("ftree1", Nothing, simpleFaultTreeMonad, [1, 3])
  , ("ftree1", Just [4, 1, 3, 2], simpleFaultTreeMonad, [])
  , ("traditional", Nothing, traditionalHydrosystemsM True >>= traditionalActuationsM True, [5e-6])
  , ("more electrical", Nothing, medianHydrosystemsM True >>= medianActuationsM True, [5e-6])
  , ("electrical", Nothing, electroHydrosystemsM True False >>= electroActuationsM False, [5e-6])
  ]

treesS :: Fractional k => [(String, Maybe [Variable], FaultTreeMonad k [Variable], [Double])]
treesS =
  [ ("voterTree", Nothing, testVoterM, [0])
  , ("ftree1", Nothing, simpleFaultTreeMonad, [1, 3])
  , ("ftree1", Just [4, 1, 3, 2], simpleFaultTreeMonad, [])
  ]

testVoterM :: Fractional k => FaultTreeMonad k [Variable]
testVoterM = do
  bases <- replicateM 100 (constantM 0.1)
  v <- foldingVoterM 20 bases
  return [v]

simpleFaultTreeMonad :: Fractional k => FaultTreeMonad k [Variable]
simpleFaultTreeMonad = do
  a <- lambdaM 15.0
  b <- lambdaM 35.0
  _ <- andM a b
  c <- lambdaM 3.0
  t <- andM a c
  return [t]

escalatorChannelM :: Fractional k => Variable -> FaultTreeMonad k Variable
escalatorChannelM hydro = do
  ccu <- lambdaM 50
  steer <- lambdaM 15
  x <- orM ccu hydro
  orM x steer

escalatorFaultTreeSesyrel1 :: Fractional k => FaultTreeMonad k [Variable]
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

escalatorFaultTreeSesyrel2 :: Fractional k => FaultTreeMonad k [Variable]
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

traditionalHydrosystemsM :: Fractional k => Bool -> FaultTreeMonad k [Variable]
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

traditionalActuationsM :: Fractional k => Bool -> [Variable] -> FaultTreeMonad k [Variable]
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

medianHydrosystemsM :: Fractional k => Bool -> FaultTreeMonad k [Variable]
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

medianActuationsM :: Fractional k => Bool -> [Variable] -> FaultTreeMonad k [Variable]
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

electroHydrosystemsM :: Fractional k => Bool -> Bool -> FaultTreeMonad k [Variable]
electroHydrosystemsM withAccum doValves = do
  [engineL, engineR] <- replicateM 2 (lambdaM 82)
  [electroGrpL, electroGrpR] <- replicateM 2 (lambdaM 60)
  electromotor1 <- lambdaM 10
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

electroActuationsM :: Fractional k => Bool -> [Variable] -> FaultTreeMonad k [Variable]
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
