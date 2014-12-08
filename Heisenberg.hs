{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Heisenberg where

-- Only single qubits!

import Control.Monad.Trans.Class
import Control.Monad
import Control.Monad.Random

import Data.Complex
import Data.List
import Data.Maybe

import System.Random

type Cmplx = Complex Double

inf :: Double
inf = read "Infinity"

newtype Psi c = Psi (c, c) deriving(Show, Eq)
deriving instance Functor (Psi)
type PsiC = Psi Cmplx

normalize :: PsiC -> PsiC
normalize v@(Psi (p, q)) =
  let mag = dot v v in Psi (p / (sqrt mag), q / (sqrt mag))

state45 :: PsiC
state45 = normalize $ Psi (1, 1)

newtype Mat c = Mat ((c, c), (c, c))  deriving(Show, Eq)
deriving instance Functor (Mat)
type MatC = Mat Cmplx

zeroM :: MatC
zeroM = Mat ((0, 0), (0, 0))

pauliI :: MatC
pauliI = Mat ((1, 0), (0, 1))

pauliX :: MatC
pauliX = Mat ((0, 1), (1, 0))

pauliY :: MatC
pauliY = Mat ((0, 0 :+ (-1)), (0 :+ 1, 0))

pauliZ :: MatC
pauliZ = Mat ((1, 0), (0, (-1)))

hadamard :: MatC
hadamard = Mat ((1 / sqrt(2), 1 / sqrt(2)), (1 / sqrt(2), (-1) / sqrt(2)))

dot :: PsiC -> PsiC -> Cmplx
dot (Psi (a, b)) (Psi (p, q)) = (conjugate a) * p + (conjugate b) * q

epsilon :: Double
epsilon = 1.0e-30

toReal :: Cmplx -> Double
toReal c = if imagPart c > epsilon then error $ "throwing away iota: " ++ show c
           else realPart c

eigenValues :: MatC -> [Cmplx]
eigenValues (Mat ((p, q), (r, s))) =
  let discr = sqrt $ (p + s) * (p + s) - 4 * (p * s - r * q)
  in nub [((p + s) - discr) / 2, ((p + s) + discr) / 2]

adjoint :: MatC -> MatC
adjoint (Mat ((a, b), (c, d))) =
  fmap conjugate $ Mat ((a, c), (b, d))

addMat :: MatC -> MatC -> MatC
addMat (Mat ((a, b), (c, d))) (Mat ((p, q), (r, s))) =
  Mat ((a + p, b + q), (c + r, d + s))

compose :: MatC -> MatC -> MatC
compose (Mat ((a, b), (c, d))) (Mat ((p, q), (r, s))) =
  Mat ((a * p + b * r, a * q + b * s), (c * p + d * r, c * q + d * s))

eigenVectForValue :: MatC -> Cmplx -> PsiC
eigenVectForValue (Mat ((p, q), (r, s))) lam =
  let slope = if (magnitude q) > epsilon
              then (lam - p) / q
              else if (magnitude (lam - s)) > epsilon
                   then r / (lam - s)
                   else error "inconsistent equations!"
      slopeIsInf = (magnitude (p - lam) > epsilon && (magnitude q) < epsilon) ||
                   (magnitude (lam - s) < epsilon && (magnitude r) > epsilon)
  in if slopeIsInf then Psi (0, 1)
     else normalize $ Psi (1, slope)

outerProduct :: PsiC -> PsiC -> MatC
outerProduct (Psi (p, q)) (Psi (r, s)) =
  let [r', s'] = map conjugate [r, s]
  in Mat ((p * r', p * s'), (q * r', q * s'))

isNormal :: MatC -> Bool
isNormal mat = (compose mat $ adjoint mat) == (compose (adjoint mat) mat)

spectral :: MatC -> Maybe [(Cmplx, MatC)]
spectral mat =
  if not (isNormal mat) then Nothing
  else let projFor eigenValue =
             let vec = eigenVectForValue mat eigenValue
             in (eigenValue, outerProduct vec vec)
       in Just $ map projFor $ eigenValues mat

apply :: MatC -> PsiC -> PsiC
apply (Mat ((p, q), (r, s))) (Psi (m, n)) = Psi (p * m + q * n, r * m + s * n)

getPossibleOutcomes :: MatC -> PsiC ->
                       Maybe [(Double, Double)] -- (result, prob)
getPossibleOutcomes mat state = do
  spectralDecomp <- spectral mat
  let getProb (eigenV, proj) =
        (toReal eigenV, toReal $ dot state (apply proj state))
  return $ map getProb spectralDecomp

type Q = RandT StdGen Maybe

data Experiment = Exp {
  getRunCount :: Int,
  getObservable :: MatC,
  getState :: PsiC,
  getRandGen :: StdGen
  } deriving(Show)

getNMeasurements :: Experiment -> Q [Double]
getNMeasurements (Exp n mat state _) = do
  probs <- lift $ getPossibleOutcomes mat state
  let withRationalWeights = map (\(x, y :: Double)->(x, toRational y)) probs
  sequence $ replicate n (fromList withRationalWeights)

runNMeasurements :: Experiment -> Maybe ([Double], StdGen)
runNMeasurements exp =
  runRandT (getNMeasurements exp) $ getRandGen exp

getStdDevFor :: Experiment -> Maybe (Double, StdGen)
getStdDevFor exp = do
  (scores, stdgen) <- runNMeasurements exp
  let n = (fromIntegral $ length scores) :: Double
      mean = (sum scores) / n
      variance = (sum $ map (\t -> (t - mean) ** 2) scores) / n
  return $ (sqrt variance, stdgen)

verifyHeisenberg runs (c, d) st stdGen =
  let runFor obs rand = fromJust $ getStdDevFor (Exp runs obs st rand)
      commutator = addMat (compose c d) $ fmap (0 -) $ compose d c
      (cStdDev, stdGen2) = runFor c stdGen
      (dStdDev, stdGen3) = runFor d stdGen2
      left = cStdDev * dStdDev
      right = (magnitude $ dot st $ apply commutator st) / 2
      -- this < 1e-5 makes feel not so good
      check = (left - right) >= 0.0 || (left - right) < 1e-5
  in ((left, right, check), stdGen3)

main :: IO ()
main =
  let observables = [pauliI, pauliX, pauliY, pauliZ, hadamard]
      testVect =
        [(matA, matB, state45) | matA <- observables, matB <- observables]
      numberedTests = zip testVect [1..]
      testOne ((a, b, c), num) = do
        t <- getStdRandom $ verifyHeisenberg (10 * 1000) (a, b) c
        return ((a, b, c), num, t)
      testFailed (_, _, (_, _, r)) = not r
  in do
    results <- sequence $ map testOne numberedTests
    print $ filter testFailed results
