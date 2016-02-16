{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}

module Main where

import Test.DocTest

main :: IO ()
main = doctest [ "src/Language/MicroKanren.hs" ]
