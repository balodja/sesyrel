import Sesyrel.FaultTree
import Sesyrel.Distribution

import Control.Monad.Writer.Strict

import Prelude hiding (Rational)
import System.IO (withFile, hFlush, hPutStrLn, IOMode(..))

main :: IO ()
main = do
  let doIt (name, mbOrder, ftreeM) = let (vars, FaultTree _ factors) = evalFaultTreeM ftreeM
                                     in case mbOrder of
                                       Nothing -> factorsSimpleProcess name (Left vars) factors
                                       Just vs -> factorsSimpleProcess name (Right vs) factors
  withFile "output.tex" WriteMode $ \h -> do
    let putLine l = hPutStrLn h l >> hFlush h
    mapM_ putLine . execWriter . mapM_ doIt $ trees

trees :: [(String, Maybe [Int], FaultTreeM [Int])]
trees =
  [ ("ftree1", Nothing, simpleFaultTreeM)
  , ("ftree1", Just [4, 1, 3, 2], simpleFaultTreeM)
  ]

testTreeM :: FaultTreeM [Int]
testTreeM = do
  a <- lambdaM 3.0
  b <- lambdaM 5.0
  c <- orM b b
  d <- orM b c
  e <- andM a c
  f <- andM c d
  return []

simpleFaultTreeM :: FaultTreeM [Int]
simpleFaultTreeM = do
  a <- lambdaM 15.0
  b <- lambdaM 35.0
  _ <- andM a b
  c <- lambdaM 3.0
  t <- andM a c
  return [t]

escalatorChannelM :: Int -> FaultTreeM Int
escalatorChannelM hydro = do
  ccu <- lambdaM 50
  steer <- lambdaM 15
  x <- orM ccu hydro
  orM x steer

escalatorFaultTree1 :: FaultTreeM [Int]
escalatorFaultTree1 = do
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

escalatorFaultTree2 :: FaultTreeM [Int]
escalatorFaultTree2 = do
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

hydrosystemsM :: FaultTreeM [Int]
hydrosystemsM = do
  [engineL, engineR] <- replicateM 2 (lambdaM 282)
  [generatorL, generatorR] <- replicateM 2 (lambdaM 125)
  [electroGrp1, electroGrp2] <- replicateM 2 (lambdaM 1060)
  [tank1, tank2, tank3] <- replicateM 3 (lambdaM 30)
  [hydroPump1, hydroPump2, hydroPump3] <- replicateM 3 (lambdaM 125)
  [electromotor1, electromotor2, electromotor3, electromotor4] <- replicateM 4 (lambdaM 100)
  [pumpStation1, pumpStation2, pumpStation3, pumpStation4] <- replicateM 4 (lambdaM 567)
  accumulator <- lambdaM 30
  
  electroSys1 <- orM engineL generatorL >>= orM electroGrp1
  electroSys2 <- orM engineL generatorR >>= orM electroGrp2
  electroSys <- andM electroSys1 electroSys2
  
  hydro2Main <- orM electroSys electromotor2 >>= orM pumpStation2
  hydro2Res1 <- orM accumulator electromotor4 >>= orM pumpStation4
  let hydro2Res2 = hydroPump2
  hydro2 <- andM hydro2Main hydro2Res1 >>= andM hydro2Res2 >>= orM tank2
  
  hydro1Main <- orM hydroPump1 engineL
  hydro3Main <- orM hydroPump3 engineR
  hydro1Res <- orM electroSys electromotor1 >>= orM pumpStation1
  hydro3Res <- orM electroSys electromotor3 >>= orM pumpStation3
  hydro1 <- andM hydro1Main hydro1Res >>= orM tank1
  hydro3 <- andM hydro3Main hydro3Res >>= orM tank3
  return [hydro1, hydro2, hydro3]

actuationsM :: [Int] -> FaultTreeM [Int]
actuationsM [hydro1, hydro2, hydro3] = do
  [ccu1, ccu2, ccu3, ccu4] <- replicateM 4 (lambdaM 50)
  [steer1, steer2, steer3, steer4] <- replicateM 4 (lambdaM 15)
  channel1 <- orM hydro1 ccu1 >>= orM steer1
  channel2 <- orM hydro2 ccu2 >>= orM steer2
  channel3 <- orM hydro2 ccu3 >>= orM steer3
  channel4 <- orM hydro3 ccu4 >>= orM steer4
  elevator1 <- andM channel1 channel2
  elevator2 <- andM channel3 channel4
  elevator <- andM elevator1 elevator2
  return [elevator]
