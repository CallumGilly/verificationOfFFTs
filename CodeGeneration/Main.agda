{-# OPTIONS --guardedness #-}

module CodeGeneration.Main where

open import CodeGeneration.DSL
open import CodeGeneration.Translate-Agda
open import CodeGeneration.Translate-C


open import IO using (IO; run; Main; _>>_; _>>=_; putStrLn)

main : Main
main = run do
  putStrLn entry
  
