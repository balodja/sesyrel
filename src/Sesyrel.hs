import Sesyrel.FaultTree
import Sesyrel.Distribution

import Control.Monad.Writer

import Prelude hiding (Rational)
import System.IO (withFile, hFlush, hPutStrLn, IOMode(..))

main :: IO ()
main = do
  let doIt (name, mbOrder, ftreeM) = let (vs, FaultTree _ factors) = evalFaultTreeM ftreeM
                                     in case mbOrder of
                                       Nothing -> factorsSimpleProcess name (Left vs) factors
                                       Just vs -> factorsSimpleProcess name (Right vs) factors
  withFile "output.tex" WriteMode $ \h -> do
    let putLine l = hPutStrLn h l >> hFlush h
    mapM_ putLine . execWriter . mapM_ doIt $ trees

trees :: [(String, Maybe [Int], FaultTreeM [Int])]
trees =
  [ ("ftree1", Nothing, simpleFaultTreeM1)
  , ("ftree1", Just [4, 1, 3, 2], simpleFaultTreeM1)
  , ("ftree2", Nothing, simpleFaultTreeM2)
  , ("ftree3", Nothing, simpleFaultTreeM3)
  , ("failed fault tree", Nothing, failedFaultTree)
  ]

simpleFaultTreeM1 :: FaultTreeM [Int]
simpleFaultTreeM1 = do
  a <- lambdaM 15.0
  b <- lambdaM 35.0
  andM a b
  c <- lambdaM 3.0
  t <- andM a c
  return [t]

simpleFaultTreeM2 :: FaultTreeM [Int]
simpleFaultTreeM2 = do
  a <- lambdaM 10.0
  b <- lambdaM 3.0
  t <- priorityAndOrM a b b
  return [t]

simpleFaultTreeM3 :: FaultTreeM [Int]
simpleFaultTreeM3 = do
  a <- lambdaM 10.0
  b <- andM a a
  c <- andM a b
  d <- orM a c
  t <- priorityAndOrM d a c
  return [t]

failedFaultTree :: FaultTreeM [Int]
failedFaultTree = do
  x1 <- lambdaM 70
  x2 <- lambdaM 70
  v <- lambdaM 10
  y1 <- priorityAndOrM v x1 x2
  y2 <- priorityAndOrM v x1 x2
  t <- orM y1 y2
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
