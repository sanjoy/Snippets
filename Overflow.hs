{-# LANGUAGE RankNTypes, NegativeLiterals #-}
import Data.Int
import Data.Word
import Data.Bits
import Data.Maybe
import Data.List
import qualified Data.Set as S
-- import Test.QuickCheck

sext :: Int8 -> Int16
sext i = fromIntegral i

zext :: Int8 -> Int16
zext i = let w = fromIntegral i :: Word8
         in fromIntegral w

udiv8 :: Int8 -> Int8 -> Int8
udiv8 a b = let result = ((fromIntegral a)::Word8) `div` ((fromIntegral b)::Word8)
            in fromIntegral result

trunc :: Int16 -> Int8
trunc i = fromIntegral i

allInt8 = [-128..127] :: [Int8]
allInt8Pairs = [(x, y) | x <- allInt8, y <- allInt8]
allInt8Triples = [(x, y, z) | x <- allInt8, y <- allInt8, z <- allInt8]
allInt8Quads = [(x, y, z, w) | x <- allInt8, y <- allInt8, z <- allInt8, w <- allInt8]

sign_overflows_op :: (Int8 -> Int8 -> Int8) -> (Int16 -> Int16 -> Int16) ->
                     Int8 -> Int8 -> Bool
sign_overflows_op a b c d = (\(_,_,r)->r) (sign_overflows_op_full a b c d)

unsign_overflows_op :: (Int8 -> Int8 -> Int8) -> (Int16 -> Int16 -> Int16) ->
                     Int8 -> Int8 -> Bool
unsign_overflows_op a b c d = (\(_,_,r)->r) (unsign_overflows_op_full a b c d)

unsign_overflows_add = unsign_overflows_op (+) (+)

sign_overflows_op_full :: (Int8 -> Int8 -> Int8) -> (Int16 -> Int16 -> Int16) ->
                          Int8 -> Int8 -> (Int16, Int16, Bool)
sign_overflows_op_full f8 f16 x y =
  let a = sext (x `f8` y)
      b = sext x `f16` sext y
  in (a, b, a /= b)

unsign_overflows_op_full :: (Int8 -> Int8 -> Int8) -> (Int16 -> Int16 -> Int16) ->
                          Int8 -> Int8 -> (Int16, Int16, Bool)
unsign_overflows_op_full f8 f16 x y =
  let a = zext (x `f8` y)
      b = zext x `f16` zext y
  in (a, b, a /= b)

sign_overflows_mul = sign_overflows_op (*) (*)
unsign_overflows_sub = unsign_overflows_op (-) (-)

getSignBit x = if x < 0 then 1 else 0::Int8

sign_overflows_shl_2 :: Int8 -> Int -> Bool
sign_overflows_shl_2 a s =
  let t = shiftL (zext a) s
      tw = fromIntegral t :: Word16
      tws = shiftR tw 8
      tws_trunc = fromIntegral tws :: Int8
      sb = (shiftL a s) `xor` (shiftL 1 s)
  in if sb >= 0
     then tws_trunc /= 0
     else (tws_trunc /= ((shiftL 1 s) - 1))

sign_overflows_shl_3 :: Int8 -> Int -> Bool
sign_overflows_shl_3 a s =
  s == 7 || sign_overflows_mul a (shiftL 1 s)

sign_overflows_shl_4 :: Int8 -> Int -> Bool
sign_overflows_shl_4 a s =
  a /= 1 && sign_overflows_shl a s

sign_overflows_shl_5 :: Int8 -> Int -> Bool
sign_overflows_shl_5 a s =
  if s == 7 then
    unsign_overflows_shl a s
  else
    sign_overflows_shl a s

sign_overflows_shl_6 :: Int8 -> Int -> Bool
sign_overflows_shl_6 a s =
  let f0 = \p q-> shiftL p (fromIntegral q)
      f1 = \p q-> shiftL p (fromIntegral q)
  in sign_overflows_op f0 f1 a (fromIntegral s)

sign_overflows_shl :: Int8 -> Int -> Bool
sign_overflows_shl a s = let t = shiftL (zext a) s
                             tw = fromIntegral t :: Word16
                             tws = shiftR tw 8
                             tws_trunc = fromIntegral tws :: Int8
                         in if shiftL a s >= 0
                            then tws_trunc /= 0
                            else (tws_trunc /= ((shiftL 1 s) - 1))

sign_overflows_shl_f :: Int8 -> Int -> (Int8, Int8, Bool)
sign_overflows_shl_f a s = let t = shiftL (zext a) s
                               tw = fromIntegral t :: Word16
                               tws = shiftR tw 8
                               tws_trunc = fromIntegral tws :: Int8
                           in (tws_trunc, shiftL a s,
                               if shiftL a s >= 0
                               then tws_trunc /= 0
                               else (tws_trunc /= ((shiftL 1 s) - 1)))

unsign_overflows_shl :: Int8 -> Int -> Bool
unsign_overflows_shl a s = let t = shiftL (zext a) s
                               tw = fromIntegral t :: Word16
                               tws = shiftR tw 8
                               tws_trunc = fromIntegral tws :: Int8
                           in tws_trunc /= 0

sign_overflows :: Int8 -> Int8 -> Bool
sign_overflows x y = sext (x + y) /= (sext x + sext y)

sign_overflows_sub :: Int8 -> Int8 -> Bool
sign_overflows_sub x y = sext (x - y) /= (sext x - sext y)

sign_overflows_sub_full :: Int8 -> Int8 -> (Bool, Int16, Int16)
sign_overflows_sub_full x y =
  let m = sext (x - y)
      n = sext x - sext y
  in (m /= n, m, n)

sign_overflows_full :: Int8 -> Int8 -> (Int16, Int16)
sign_overflows_full x y = (sext (x + y), (sext x + sext y))

unsign_overflows :: Int8 -> Int8 -> Bool
unsign_overflows x y = zext (x + y) /= (zext x + zext y)

unsign_overflows_mul :: Int8 -> Int8 -> Bool
unsign_overflows_mul x y = zext (x * y) /= (zext x * zext y)

urange :: Int8 -> Int8 -> [Int8]
urange a b = if a == b then [] else a:urange (a+1) b

ult8 :: Int8 -> Int8 -> Bool
ult8 x y = ((fromIntegral x)::Word8) < ((fromIntegral y)::Word8)

ugt8 :: Int8 -> Int8 -> Bool
ugt8 x y = ult8 y x

ule8 :: Int8 -> Int8 -> Bool
ule8 x y = not(ugt8 x y)

uge8 :: Int8 -> Int8 -> Bool
uge8 x y = not(ult8 x y)

ult16 :: Int16 -> Int16 -> Bool
ult16 x y = ((fromIntegral x)::Word16) < ((fromIntegral y)::Word16)


log2 :: Int8 -> Int8
log2 n
    | n < 1     = error "agument of logarithm must be positive"
    | otherwise = go 0 1
      where
        go exponent prod
            | prod < n  = go (exponent + 1) (2*prod)
            | otherwise = exponent

mul_lohi :: Int8 -> Int8 -> (Int8, Int8) -- (lo, hi)
mul_lohi x y = let x' = zext x
                   y' = zext y
                   m = x' * y'
               in (fromIntegral m, fromIntegral (m `rotateR` 8))


clz :: Int8 -> Int
clz x = let asBool = reverse $ map (testBit x) [0..7]
        in case elemIndex True asBool of
            Just x -> x
            Nothing -> 8

clo :: Int8 -> Int
clo x = let asBool = reverse $ map (testBit x) [0..7]
        in case elemIndex False asBool of
            Just x -> x
            Nothing -> 8

cls :: Int8 -> Int
cls x = max (clo x) (clz x)

toBin :: Word8 -> String
toBin w = map (\i->if testBit w i then '1' else '0') [0..7]

log_floor :: Word8 -> Int
log_floor x = foldl1 max $ filter (\i -> (shift 1 i) <= x) [0..7]

log_ceil :: Word8 -> Int
log_ceil x = foldl1 min $ filter (\i -> (shift 1 i) >= x) [0..7]

---

w :: Int8 -> Bool
w x = not (unsign_overflows_mul (-1) x)

w2 :: Int8 -> Bool
w2 x = sign_overflows_sub 0 x /= sign_overflows_mul (-1) x

w3 :: Int8 -> Bool
w3 x = unsign_overflows_sub 0 x /= unsign_overflows_mul (-1) x

w4 :: (Int8, Int8) -> Bool
w4 (a, b) = b /= 0 && a + b == a

w5 :: (Int8, Int8) -> Bool
w5 (x, y) = (x < y) /= ((x + (-128)) `ult8` (y + (-128)))

w6 :: (Int8, Int8) -> Bool
w6 (x, y) = sign_overflows_op (-) (-) x y /= sign_overflows_op (+) (+) x (-y)

-- w8 :: Int8 -> Bool
-- w8 x = let ma = if x + 1 > x then x + 1 else x
--            mi = if x + 1 < x then x + 1 else x
--        in (ma - mi) /

-- main = print $ filter w8 allInt8

w7 :: (Int8, Int8) -> Bool
w7 (x, y) = (x > y) /= ((comp x) < (comp y))
    where comp t = (-1) - t


w8 :: (Int8, Int8, Int8) -> Bool
w8 (e, s, stride) =
    let computed_trip_count = ((e - s) + stride - 1) `udiv8` stride
        is_zero_trip_count = not(s < e)
        is_protected = (s - stride) < e
    in is_protected && is_zero_trip_count && computed_trip_count /= 0

w8_full (e, s, stride) =
    let computed_trip_count = ((e - s) + stride - 1) `udiv8` stride
        is_zero_trip_count = not(s < e)
        is_protected = (s - stride) < e
        result = is_protected && is_zero_trip_count && computed_trip_count /= 0
    in (computed_trip_count, is_zero_trip_count, is_protected, result)

--    (e - s) `ugt8` 1 && (e - s) `ule8` 128 && s >= e && (s + 128) < e


w9 :: (Int8, Int8, Int8) -> Bool
w9 (e, s, stride) =
    let computed_trip_count = ((e - s) + stride - 1) `udiv8` stride
        is_zero_trip_count = not(s `ult8` e)
        is_protected = (s - stride) `ult8` e
    in is_protected && is_zero_trip_count && computed_trip_count /= 0

w10 :: (Int8, Int8, Int8) -> Bool
w10 (e, s, stride) =
    let computed_trip_count = ((e - s) + stride - 1) `udiv8` stride
        is_zero_trip_count = not(s `ult8` e)
        is_one_trip_count = s `ult8` e && not (unsign_overflows_add s stride) && (not $ (s + stride) `ult8` e)
        is_protected = (s - stride) `ult8` e
    in is_protected && is_one_trip_count && computed_trip_count /= 1

--w10_full :: (Int8, Int8, Int8) -> Bool
w10_full (e, s, stride) =
    let computed_trip_count = ((e - s) + stride - 1) `udiv8` stride
        is_zero_trip_count = not(s `ult8` e)
        is_one_trip_count = s `ult8` e && not (unsign_overflows_add s stride) && (not $ (s + stride) `ult8` e)
        is_protected = (s - stride) `ult8` e
        result = is_protected && is_one_trip_count && computed_trip_count /= 1
    in (is_protected, is_one_trip_count, computed_trip_count, result)
