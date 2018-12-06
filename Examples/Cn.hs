{- Examples found in JM's master thesis, p. 228 (pdf)
 - -}
module Examples.Cn where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Logic
import NMatrix
import Signature
import Control.Exception.Safe (SomeException)
import Data.Either
import Formula
import Semantics

a1 = read "{} | ==>(a, ==>(b, a))" :: Consequence
a2 = read "{} | ==>(==>(a, b), ==>(==>(a, ==>(b, c)),==>(a, c)))" :: Consequence
a3 = read "{} | ==>(a, ==>(b, <*>(a, b)))" :: Consequence
a4 = read "{} | ==>(<*>(a, b), a)" :: Consequence
a5 = read "{} | ==>(<*>(a, b), b)" :: Consequence
a6 = read "{} | ==>(a, <+>(a, b))" :: Consequence
a7 = read "{} | ==>(b, <+>(a, b))" :: Consequence
a8 = read "{} | ==>(==>(a, c), ==>(==>(b, c), ==>(<+>(a, b), c)))" :: Consequence
a9 = undefined
a10 = undefined
a11 = read "{} | <+>(a, -(a))" :: Consequence
a12 = read "{} | ==>(-(-(a)), a)" :: Consequence
mp = read "{==>(a, b), a} | b" :: Consequence


cnConseqs = S.fromList 
                [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, mp] :: ConsequenceRelation

cnSignature = sigmaFromConseqRelation cnConseqs :: Either SomeException Signature
