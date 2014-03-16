import Sesyrel.FaultTree
import Sesyrel.Distribution

import Control.Monad.Writer

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
  [tank1, tank2] <- replicateM 2 (lambdaM 30)
  [engine1, engine2] <- replicateM 2 (lambdaM 282)
  [electroGrp1, electroGrp2] <- replicateM 2 (lambdaM 1060)
  [hydroPump1, hydroPump2] <- replicateM 2 (lambdaM 125)
  electromotors <- replicateM 2 (lambdaM 100)
  pumpStations <- replicateM 2 (lambdaM 567)
  mechanics1 <- orM tank1 engine1
  mechanics2 <- orM tank2 engine2
  electroSys1 <- orM mechanics1 electroGrp1
  electroSys2 <- orM mechanics2 electroGrp2
  electroSys <- andM electroSys1 electroSys2
  hydro1Main <- orM hydroPump1 mechanics1
  hydro2Main <- orM hydroPump1 mechanics1
  hydro1Res <- orM electroSys (electromotors !! 0) >>= orM (pumpStations !! 0)
  hydro2Res <- orM electroSys (electromotors !! 1) >>= orM (pumpStations !! 1)
  hydro1 <- andM hydro1Main hydro1Res
  hydro2 <- andM hydro2Main hydro2Res
  return [hydro1, hydro2]
