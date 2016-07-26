limit :: Integer
limit = 2233393

f :: Integer -> Integer
f x = (1 + x + x * x + x * x * x * x) `rem` limit
