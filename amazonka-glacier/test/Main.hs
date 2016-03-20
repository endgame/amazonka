{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- |
-- Module      : Main
-- Copyright   : (c) 2013-2016 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
module Main (main) where

import Test.Tasty
import Test.AWS.Glacier
import Test.AWS.Glacier.Internal

main :: IO ()
main = defaultMain $ testGroup "Glacier"
    [ testGroup "tests"    tests
    , testGroup "fixtures" fixtures
    ]
