{-# LANGUAGE OverloadedStrings #-}
module Axiomatization (getAxiomatization, getDefaultConnective) where

import Prelude hiding (and, or)
import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Either
import Data.Maybe
import Logic
import Signature
import NMatrix
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)

impliesTruthTable = mkTruthTable [([0, 0], 1),
                                  ([0, 1], 1),
                                  ([1, 0], 0),
                                  ([1, 1], 1)] :: Either SomeException (TruthTable Int)

negationTruthTable = mkTruthTable [([0], 1),
                                   ([1], 0)] :: Either SomeException (TruthTable Int)

andTruthTable = mkTruthTable [([0, 0], 0),
                              ([0, 1], 0),
                              ([1, 0], 0),
                              ([1, 1], 1)] :: Either SomeException (TruthTable Int)

orTruthTable = mkTruthTable [([0, 0], 0),
                             ([0, 1], 1),
                             ([1, 0], 1),
                             ([1, 1], 1)] :: Either SomeException (TruthTable Int)

implies = ("==>", fromRight M.empty impliesTruthTable)
negation = ("-", fromRight M.empty negationTruthTable)
and = ("*", fromRight M.empty andTruthTable)
or = ("+", fromRight M.empty orTruthTable)

connectives = [implies, negation, and, or] 

getDefaultConnective :: [(String, TruthTable Int)]
getDefaultConnective = connectives

-- S2 Axiomatization - 2(v)

s2_1 = read "{P} | +(P, Q)" :: Consequence
s2_2 = read "{+(P, P)} | P" :: Consequence
s2_3 = read "{+(P, Q)} | +(Q, P)" :: Consequence
s2_4 = read "{+(P, +(Q, R))} | +(+(P, Q), R)" :: Consequence

s2Axiomatization = [s2_1, s2_2, s2_3, s2_4]
s2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList s2Axiomatization)

-- A4 Axiomatization - 2(v,^)

a4_5 = read "{+(R, P), +(R, Q)} | +(R, *(P, Q))" :: Consequence
a4_6 = read "{+(R, *(P, Q))} | +(R, P)" :: Consequence
a4_7 = read "{+(R, *(P, Q))} | +(R, Q)" :: Consequence

a4Axiomatization = s2Axiomatization ++ [a4_5, a4_6, a4_7]
a4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList a4Axiomatization)

-- TODO: Implement!
getAxiomatization :: Signature -> [Consequence]
getAxiomatization signature
    | signature == s2Signature = s2Axiomatization -- 2(v)
    | signature == a4Signature = a4Axiomatization -- 2(v,^)
    | otherwise                = []
