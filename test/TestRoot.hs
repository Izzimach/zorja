module Main (main) where

import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck
import Test.HUnit
--import Zorja.Patchable

test1 :: Test
test1 = TestCase (assertEqual "for (1+2)," (3 :: Integer) (1+2))

testList :: Test
testList = TestList [test1]

main :: IO b
main = do
    (Counts _caseCount _tryCount errCount failCount) <- runTestTT testList
    if (errCount + failCount == 0)
        then exitSuccess
        else exitFailure