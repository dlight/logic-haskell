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

zeroTruthTable = mkTruthTable [([], 0)] :: Either SomeException (TruthTable Int)

oneTruthTable = mkTruthTable [([], 1)] :: Either SomeException (TruthTable Int)

negationTruthTable = mkTruthTable [([0], 1),
                                   ([1], 0)] :: Either SomeException (TruthTable Int)

impliesTruthTable = mkTruthTable [([0, 0], 1),
                                  ([0, 1], 1),
                                  ([1, 0], 0),
                                  ([1, 1], 1)] :: Either SomeException (TruthTable Int)

andTruthTable = mkTruthTable [([0, 0], 0),
                              ([0, 1], 0),
                              ([1, 0], 0),
                              ([1, 1], 1)] :: Either SomeException (TruthTable Int)

orTruthTable = mkTruthTable [([0, 0], 0),
                             ([0, 1], 1),
                             ([1, 0], 1),
                             ([1, 1], 1)] :: Either SomeException (TruthTable Int)

kaTruthTable = mkTruthTable [([0, 0, 0], 0),
                             ([0, 0, 1], 0),
                             ([0, 1, 0], 0),
                             ([0, 1, 1], 0),
                             ([1, 0, 0], 0),
                             ([1, 0, 1], 1),
                             ([1, 1, 0], 1),
                             ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)

kiTruthTable = mkTruthTable [([0, 0, 0], 0),
                             ([0, 0, 1], 0),
                             ([0, 1, 0], 0),
                             ([0, 1, 1], 0),
                             ([1, 0, 0], 1),
                             ([1, 0, 1], 1),
                             ([1, 1, 0], 0),
                             ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)

adTruthTable = mkTruthTable [([0, 0, 0], 0),
                             ([0, 0, 1], 0),
                             ([0, 1, 0], 1),
                             ([0, 1, 1], 0),
                             ([1, 0, 0], 1),
                             ([1, 0, 1], 1),
                             ([1, 1, 0], 1),
                             ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)


zero = ("/", fromRight M.empty zeroTruthTable)
one = (".", fromRight M.empty oneTruthTable)
implies = ("==>", fromRight M.empty impliesTruthTable)
negation = ("-", fromRight M.empty negationTruthTable)
and = ("*", fromRight M.empty andTruthTable)
or = ("+", fromRight M.empty orTruthTable)
ka = ("+*", fromRight M.empty kaTruthTable)
ki = (">*", fromRight M.empty kiTruthTable)
ad = ("+-", fromRight M.empty adTruthTable)

connectives = [zero, one, implies, negation, and, or, ka, ki, ad]

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

-- F_6^\inf Axiomatization - 2(ka)

f6_1 = read "{A, P} | +*(A, P, Q)" :: Consequence
f6_2 = read "{+*(A, P, P)} | P" :: Consequence
f6_3 = read "{+*(A, P, Q)} | +*(A, Q, P)" :: Consequence
f6_4 = read "{+*(A, P, +*(A, Q, R))} | +*(A, +*(A, P, Q), R)" :: Consequence
f6_5 = read "{+*(B, R, A), +*(B, R, +*(B, P, Q))} | +*(B, R, +*(A, P, Q))" :: Consequence
f6_6 = read "{+*(B, R, +*(A, P, Q))} | +*(B, R, A)" :: Consequence
f6_7 = read "{+*(B, R, +*(A, P, Q))} | +*(B, R, +*(B, P, Q))" :: Consequence

f6Axiomatization = [f6_1, f6_2, f6_3, f6_4, f6_5, f6_6, f6_7]
f6Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f6Axiomatization)

-- F_5^\inf Axiomatization - 2(ki)

f5_1 = read "{P, >*(A, P, Q)} | Q" :: Consequence
f5_2 = read "{A} | >*(A, P, >*(A, Q, P))" :: Consequence
f5_3 = read "{>*(B, T, A)} | >*(B, T, >*(A, >*(A, P, >*(A, Q, R)), >*(A, P, R)))" :: Consequence
f5_4 = read "{>*(B, T, A)} | >*(B, T, >*(A, >*(A, >*(A, P, Q), P), P))" :: Consequence
f5_5 = read "{>*(A, P, >*(A, Q, R))} | >*(A, >*(P, P, Q), R)" :: Consequence
f5_6 = read "{>*(A, >*(P, P, Q), R)} | >*(A, P, >*(A, Q, R))" :: Consequence
f5_7 = read "{>*(B, R, A), >*(B, R, >*(B, P, Q))} | >*(B, R, >*(A, P, Q))" :: Consequence
f5_8 = read "{>*(B, R, >*(A, P, Q))} | >*(B, R, A)" :: Consequence
f5_9 = read "{>*(B, R, >*(A, P, Q))} | >*(B, R, >*(B, P, Q))" :: Consequence

f5Axiomatization = [f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f5_7, f5_8, f5_9]
f5Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f5Axiomatization)

-- F_7^\inf Axiomatization - 2(ka,0)

f7_0 = read "{+*(A, P, /())} | +*(A, P, Q)" :: Consequence

f7Axiomatization = f6Axiomatization ++ [f7_0]
f7Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f7Axiomatization)

-- F_8^\inf Axiomatization - 2(ki,0)

f8_0 = read "{>*(A, P, /())} | >*(A, P, Q)" :: Consequence

f8Axiomatization = f5Axiomatization ++ [f8_0]
f8Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f8Axiomatization)

-- F_1^\inf Axiomatization - 2(ad)

f1_1 = read "{P, +-(Q, A, P)} | Q" :: Consequence
f1_2 = read "{A} | +-(+-(P, A, Q), A, P)" :: Consequence
f1_3 = read "{+-(A, B, T)} | +-(+-(+-(R, A, P), A, +-(+-(R, A, Q), A, P)), B , T)" :: Consequence
f1_4 = read "{+-(A, B, T)} | +-(+-(P, A, +-(P, A, +-(Q, A, P))), B, T)" :: Consequence
f1_5 = read "{+-(Q, A, P)} | +-(A, Q, A)" :: Consequence
f1_6 = read "{Q} | +-(Q, A, P)" :: Consequence
f1_7 = read "{+-(+-(Q, R, Q), A, P)} | +-(+-(Q, A, P), +-(R, A, P), +-(Q, A, P))" :: Consequence
f1_8 = read "{+-(+-(Q, A, P), +-(R, A, P), +-(Q, A, P))} | +-(+-(Q, R, Q), A, P)" :: Consequence
f1_9 = read "{+-(P, B, R), +-(Q, A, P)} | +-(Q, B, R)" :: Consequence
f1_10 = read "{+-(+-(R, B, Q), A, P)} | +-(+-(R, A, P), +-(R, B, Q), +-(R, A, P))" :: Consequence
f1_11 = read "{+-(+-(R, A, P), +-(R, B, Q), +-(R, A, P))} | +-(+-(R, B, Q), A, P)" :: Consequence
f1_12 = read "{+-(P, P, P)} | P" :: Consequence
f1_13 = read "{+-(P, Q, P)} | +-(Q, P, Q)" :: Consequence
f1_14 = read "{+-(P, +-(Q, R, Q), P)} | +-(+-(P, Q, P), R, +-(P, Q, P))" :: Consequence
f1_15 = read "{+-(S, P, S), +-(S, +-(Q, A, P), S)} | +-(S, Q, S)" :: Consequence
f1_16 = read "{+-(S, A, S)} | +-(S, +-(+-(P, A, Q), A, P), S)" :: Consequence
f1_17 = read "{+-(S, +-(A, B, T), S)} | +-(S, +-(+-(+-(+-(R, A, P), A, +-(Q, A, P)), A, +-(+-(R, A, Q), A, P)), B, T), S)" :: Consequence
f1_18 = read "{+-(S, +-(A, B, T), S)} | +-(S, +-(+-(P, A, +-(P, A, +-(Q, A, P))), B, T), S)" :: Consequence
f1_19 = read "{+-(S, +-(Q, A, P), S)} | +-(S, +-(A, Q, A), S)" :: Consequence
f1_20 = read "{+-(S, Q, S)} | +-(S, +-(Q, A, P), S)" :: Consequence
f1_21 = read "{+-(S, +-(+-(Q, R, Q), A, P), S)} | +-(S, +-(+-(Q, A, P), +-(R, A, P), +-(Q, A, P)), S)" :: Consequence
f1_22 = read "{+-(S, +-(+-(Q, A, P), +-(R, A, P), +-(Q, A, P)), S)} | +-(S, +-(+-(Q, R, Q), A, P), S)" :: Consequence
f1_23 = read "{+-(S, +-(P, B, R), S), +-(S, +-(Q, A, P), S)} | +-(S, +-(Q, B, R), S)" :: Consequence
f1_24 = read "{+-(S, +-(+-(R, B, Q), A, P), S)} | +-(S, +-(+-(R, A, P), +-(R, P, Q), +-(R, A, Q)), S)" :: Consequence
f1_25 = read "{+-(S, +-(+-(R, A, P), +-(R, P, Q), +-(R, A, Q)), S)} | +-(S, +-(+-(R, B, Q), A, P), S)" :: Consequence

f1Axiomatization = [f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f1_7, f1_8, f1_9, f1_10, f1_11, f1_12, f1_13, f1_14, f1_15, f1_16, f1_17, f1_18, f1_19, f1_20, f1_21, f1_22, f1_23, f1_24, f1_25]
f1Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f1Axiomatization)

-- TODO: F_i^\inf 2 \leq i \leq 4

-- TODO: Implement!
getAxiomatization :: Signature -> [Consequence]
getAxiomatization signature
    | signature == s2Signature = s2Axiomatization -- 2(v)
    | signature == a4Signature = a4Axiomatization -- 2(v,^)
    | signature == f6Signature = f6Axiomatization -- 2(ka)
    | signature == f5Signature = f5Axiomatization -- 2(ki)
    | signature == f7Signature = f7Axiomatization -- 2(ka,0)
    | signature == f8Signature = f8Axiomatization -- 2(ki,0)
    | signature == f1Signature = f1Axiomatization -- 2(ad)
    | signature == f1Signature = f1Axiomatization -- 2(ad)
    | otherwise                = []
