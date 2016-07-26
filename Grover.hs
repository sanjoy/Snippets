module Grover where

isNormal :: [Double] -> Bool
isNormal fs = (sum $ map (\x-> x * x) fs) `eql` 1.0
  where eql a b = abs (a - b) < eps
        eps = 1.0e-12

replace :: [a] -> Int -> a -> [a]
replace (v:vs) 0   newval = newval:vs
replace (v:vs) idx newval = v:replace vs (idx - 1) newval
replace [] _ _ = []

g :: Int -> [Double] -> [Double]
g idx fs =
  let signFlipped = replace fs idx (- (fs !! idx))
      mean = sum signFlipped / (fromIntegral $ length signFlipped)
  in map (\x -> 2 * mean - x) signFlipped

initFor :: Int -> [Double]
initFor x = take (2 ^ x) $ repeat (1.0 / (sqrt (2 ^ x)))

example :: Int -> Int -> [[Double]]
example k l =
  let n = 2 ^ k
      states = iterate (g l) (initFor k)
  in states
