module UsingHeadJuly2015 where

import Data.List

f :: Integer -> [(Integer, Integer)]
f 0 = []
f 1 = [(0,0)]
f 2 = undefined
f 3 = [(1,0)]
f k = let (q, r) = divMod k 4 in
  case r of
    0 -> let inner = f q
         in map (\(three, four)->(three, four + 1)) inner
    1 -> let inner = f q
         in (0,0):inner
    2 -> let inner = f (q - 2)
         in (0,0):(2,0):map (\(three, four)->(three, four + 1)) inner
    3 -> let inner = f q
         in (1,0):map (\(three, four)->(three, four + 1)) inner

verify :: Integer -> Bool
verify i = let result = f i
               noReps = length(nub result) == length result
               resultComputes = sum $ map (\(t, f)-> (3 ^ t) * (4 ^ f)) result
           in noReps && resultComputes == i
