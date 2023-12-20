
module Main where

-- import qualified Math (someFunc)
import Math.NumberTheory.Factor

main :: IO ()
main = do
    print (pfactors (2))
    -- putStrLn "Hello, Haskell!"
    -- MyLib.someFunc