import Control.Monad
import System.Environment
import System.Random

main = do
  args <- liftM (map read) getArgs
  if length args /= 2 then
    putStrLn "Usage: ./Random { element-count } { limit }"
    else
    let extract = take (args !! 0) . map (abs . flip rem (args !! 1))
    in (liftM (extract . randoms) getStdGen :: IO [Int]) >>= print
