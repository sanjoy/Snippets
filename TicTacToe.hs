-- Type level two player Tic Tac Toe
-- Sanjoy Das (http://playingwithpointers.com)

-- "Formal methods will never have a significant impact until they can
--  be used by people that don't understand them." > Tom Melham

-- Inspiration:  `Type Leve Insanity', The Monad Reader 8

{-# LANGUAGE MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             UndecidableInstances,
             ScopedTypeVariables #-}

-- This game is at the "type-level" in the sense that invalid move
-- sequences raise errors from the type checker.  The "game" is
-- designed to be "played" inside GHCi, this way:
--
-- *Main> let k0 = move emptyB (a, a)
-- *Main> let k1 = move k0     (b, a)
-- *Main> printBoard k1
-- X--
-- O--
-- ---
--  ( ... try a duplicate move ... )
-- *Main> let k2 = move k1 (a, a)
--
-- <interactive>:1:10:
--     Couldn't match type `F' with `T'
--     When using functional dependencies to combine
--       And F T F,
--         arising from the dependency `a b -> c'
--   ...

-- A game is finished once there are no moves to play or when a player
-- has already won.  Trying to make a move in either of the two cases
-- raises a type error.

-- There is a second example at the end of the file.

import Data.List

-- For convenience's sake, the rows and columns are numbered
-- alphabetically.
class Row a where numeric :: a -> Int
data A
data B
data C

instance Row A where numeric _ = 0
instance Row B where numeric _ = 1
instance Row C where numeric _ = 2

-- A Pos is a position where we can place a move.  coord is used when
-- printing things, it is one of the few values around here.
class Pos a where coord :: a -> (Int, Int)
instance (Row a, Row b) => Pos (a, b) where
  coord _ = (numeric (undefined::a), numeric (undefined::b))

-- Truth and deceit.
data T
data F

-- Some basic operators.
class Same a b c | a b -> c

instance Same A A T
instance Same A B F
instance Same A C F

instance Same B A F
instance Same B B T
instance Same B C F

instance Same C A F
instance Same C B F
instance Same C C T

class And a b c | a b -> c
instance And F F F
instance And F T F
instance And T F F
instance And T T T

class Not a b | a -> b
instance Not T F
instance Not F T

-- De Morgan's
class Or a b c | a b -> c
instance (Not a a', Not b b', And a' b' c', Not c' c) =>
         Or a b c

-- Sameness for tuples.
instance (Same a c e, Same b d f, And e f result) =>
         Same (a, b) (c, d) result

class Different a b c | a b -> c
instance (Same a b result', Not result' result) =>
         Different a b result

-- Predicate for checking if a particular position is free in a board
-- or not.
class Free board move result | board move -> result
instance Free () a T
instance (Free rest move f, Different move latestMove d,
          And f d result) =>
         Free (latestMove, rest) move result

-- Make a (necessarily) valid move.
class Move b p newB | b p -> newB where
  move :: b -> p -> newB
instance (Pos p, Free b p T, GameOver b F) =>
         Move b p (p, b) where
  move = undefined

-- A board is "list of occupied positions" in most recent first order.
-- It not a list in the classic sense, the classical list [a, b, c] is
-- represented as (a, (b, (c, ()))).
class Board a where coords :: a -> [(Int, Int)]
instance Board () where coords _ = []
instance (Board rest, Pos a) => Board (a, rest) where
  coords _ = coord (undefined::a):coords (undefined::rest)

-- Inverse of Free
class Taken board pos result | board pos -> result
instance (Free board pos res', Not res' result) =>
         Taken board pos result

-- The next four predicates detect winning configurations.  The first
-- three predicates don't differentiate between the two players.  The
-- system works by dividing up the board into two sub-boards, each
-- corresponding to one player and then calling these predicates on
-- these sub-boards seaprately.

-- Check if the sub-board has a horizontal or vertical line.  This
-- checks for a horizontal or vertical like passing through (const,
-- const).
class BoardHasLine board const result | board const -> result
instance (Taken board (const, A) c0,
          Taken board (const, B) c1,
          Taken board (const, C) c2,
          Taken board (A, const) r0,
          Taken board (B, const) r1,
          Taken board (C, const) r2,
          And c0 c1 c', And c' c2 c,
          And r0 r1 r', And r' r2 r,
          Or c r result) =>
         BoardHasLine board const result

-- Check if the sub-board a diagonal.
class BoardHasDiag board result | board -> result
instance (Taken board (A, A) a0,
          Taken board (B, B) a1,
          Taken board (C, C) a2,
          Taken board (C, A) b0,
          Taken board (A, C) b2,
          And a0 a1 a', And a' a2 a,
          And b0 a1 b', And b' b2 b,
          Or a b result) =>
         BoardHasDiag board result

-- Check if the sub-board is in a winning configuration.
class Winning board result | board -> result
instance (BoardHasDiag board r0,
          BoardHasLine board A r1,
          BoardHasLine board B r2,
          BoardHasLine board C r3,
          Or r0 r1 r4, Or r2 r4 r5, Or r3 r5 result) =>
         Winning board result

-- Used to divide the board into sub-boards corresponding to each
-- player.
class Filter board player subboard | board player -> subboard
instance Filter () a ()
instance (Filter rest F restR) => Filter (a, rest) T (a, restR)
instance (Filter rest T restR) => Filter (a, rest) F restR

-- Predicate to check if somebody won.
class GameOver board result | board -> result
instance (Filter board T playerA, Filter board F playerB,
          Winning playerA a, Winning playerB b,
          Or a b result) =>
         GameOver board result

-- IO action to print a board.  Useful from within GHCi.
printBoard board =
  let coordinates = reverse $ coords board
      locations =
        (reverse . snd) $ foldl annotate (True, []) coordinates
      locations' = sortBy compareLoc locations
      marked     = markLocs locations' [(x, y) | x <- [0..2],
                                       y <- [0..2]]
      linear     = map (toC . fst) marked
      toC x      = case x of
        Nothing    -> '-'
        Just True  -> 'X'
        Just False -> 'O'
  in putStrLn $ breakLines linear
  where
    annotate (flag, list) posn = (not flag, (flag, posn):list)
    markLocs [] a = map (\a -> (Nothing, a)) a
    markLocs ((f, c):as) (b:bs) =
      if c == b then (Just f, c):markLocs as bs
      else (Nothing, b) : markLocs ((f, c):as) bs
    breakLines list =
      let (a, rest0) = splitAt 3 list
          (b, c) = splitAt 3 rest0
      in a ++ "\n" ++ b ++ "\n" ++ c
    compareLoc (_, a) (_, b) = compare a b

-- Simple values to get started.  This way the player does not have
-- type type in things like (undefined::(A, B)) and can just say (a,
-- b) instead.
a = undefined::A
b = undefined::B
c = undefined::C
emptyB = undefined::()

-- An exceedingly dumb game that illustrates what has been done here.
-- Uncommenting the two commented lines result in a type error -- the
-- game has already been won in k6.
dumbGame = let k0 = move emptyB (a, a)
               k1 = move k0     (a, b)
               k2 = move k1     (a, c)
               k3 = move k2     (b, a)
               k4 = move k3     (b, b)
               k5 = move k4     (b, c)
               k6 = move k5     (c, a)
--               k7 = move k6     (c, b)
--               k8 = move k7     (c, c)
           in printBoard k6

