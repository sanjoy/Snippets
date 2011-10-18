{-# LANGUAGE TemplateHaskell #-}

module GenerateMatcher(generateMatcher) where

import Language.Haskell.TH

generateMatcher :: String -> [String] -> Q [Dec]
generateMatcher name strs =
  return [FunD (mkName name) (map thMagic strs ++ baseCase)]
  where
    thMagic str = Clause [transform str] (NormalB (ConE 'True)) []
    baseCase = [Clause [WildP] (NormalB (ConE 'False)) []]
    transform [] = ConP (mkName "[]") []
    transform ('?':rest) =
      let colon = mkName ":" in (InfixP WildP colon $ transform rest)
    transform (x:rest) =
      InfixP (LitP (CharL x)) (mkName ":") $ transform rest
