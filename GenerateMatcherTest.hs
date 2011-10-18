{-# LANGUAGE TemplateHaskell #-}

import GenerateMatcher

generateMatcher "generatedF" ["asdf", "a?foo", "P"]

main = do
  str <- getLine
  putStrLn $ show $ generatedF str
