{-# LANGUAGE OverloadedStrings #-}
module Axiomatization where

import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L
import Data.Either
import Data.Maybe
import Logic
import Signature
import NMatrix
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)

zeroTruthTable = mkTruthTable [([], 0)] :: Either SomeException (TruthTable Int)

oneTruthTable = mkTruthTable [([], 1)] :: Either SomeException (TruthTable Int)

zeroIdentityTruthTable = mkTruthTable [([0], 0),
                                       ([1], 0)] :: Either SomeException (TruthTable Int)

oneIdentityTruthTable = mkTruthTable [([0], 1),
                                      ([1], 1)] :: Either SomeException (TruthTable Int)

negationTruthTable = mkTruthTable [([0], 1),
                                   ([1], 0)] :: Either SomeException (TruthTable Int)

impliesTruthTable = mkTruthTable [([0, 0], 1),
                                  ([0, 1], 1),
                                  ([1, 0], 0),
                                  ([1, 1], 1)] :: Either SomeException (TruthTable Int)

coimpliesTruthTable = mkTruthTable [([0, 0], 0),
                                    ([0, 1], 1),
                                    ([1, 0], 0),
                                    ([1, 1], 0)] :: Either SomeException (TruthTable Int)

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

akTruthTable = mkTruthTable [([0, 0, 0], 0),
                             ([0, 0, 1], 0),
                             ([0, 1, 0], 0),
                             ([0, 1, 1], 1),
                             ([1, 0, 0], 1),
                             ([1, 0, 1], 1),
                             ([1, 1, 0], 1),
                             ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)

xorTruthTable = mkTruthTable [([0, 0, 0], 0),
                              ([0, 0, 1], 1),
                              ([0, 1, 0], 1),
                              ([0, 1, 1], 0),
                              ([1, 0, 0], 1),
                              ([1, 0, 1], 0),
                              ([1, 1, 0], 0),
                              ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)

dTruthTable = mkTruthTable [([0, 0, 0], 0),
                            ([0, 0, 1], 0),
                            ([0, 1, 0], 0),
                            ([0, 1, 1], 1),
                            ([1, 0, 0], 0),
                            ([1, 0, 1], 1),
                            ([1, 1, 0], 1),
                            ([1, 1, 1], 1)] :: Either SomeException (TruthTable Int)

zero = ("$", fromRight M.empty zeroTruthTable)
one = (".", fromRight M.empty oneTruthTable)
zeroIdentity = ("$", fromRight M.empty zeroIdentityTruthTable)
oneIdentity = (".", fromRight M.empty oneIdentityTruthTable)
implies = ("==>", fromRight M.empty impliesTruthTable)
coimplies = ("-<", fromRight M.empty coimpliesTruthTable)
negation = ("-", fromRight M.empty negationTruthTable)
and_ = ("*", fromRight M.empty andTruthTable)
or_ = ("+", fromRight M.empty orTruthTable)
ka = ("+*", fromRight M.empty kaTruthTable)
ki = (">*", fromRight M.empty kiTruthTable)
ad = ("+-", fromRight M.empty adTruthTable)
ak = ("*+", fromRight M.empty akTruthTable)
xor = ("++", fromRight M.empty xorTruthTable)
d = (">", fromRight M.empty dTruthTable)

dm :: Int -> (String, TruthTable Int)
dm 2 = d
dm m = (">" ++ name, fromRight M.empty ttdm)
    where
        (name, tt) = dm $ m-1 
        values = S.fromList [0, 1]
        ttdm = mkTruthTable $ zip (generateTruthTableArgs (m + 1) values) ((replicate (2^m - 1) 0) ++ [1] ++ (M.elems tt))

userConnectives = [zero, one, implies, coimplies, negation, and_, or_, ka, ki, ad, ak, xor, d]
systemConnectives = [zeroIdentity, oneIdentity, implies, coimplies, negation, and_, or_, ka, ki, ad, ak, xor, d]

getUserConnectives :: [(String, TruthTable Int)]
getUserConnectives = userConnectives

getSystemConnectives :: [(String, TruthTable Int)]
getSystemConnectives = systemConnectives ++ map dm [2..]

-- R4 Axiomatization - 2(\lnot)
r4_1 = read "{P} | -(-(P))" :: Consequence
r4_2 = read "{-(-(P))} | P" :: Consequence
r4_3 = read "{P, -(P)} | Q" :: Consequence
r4Axiomatization = [r4_1, r4_2, r4_3]
r4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList r4Axiomatization)

-- R6 Axiomatization - 2(1)
r6_1 = read "{} | .()" :: Consequence
r6Axiomatization = [r6_1]
r6Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList r6Axiomatization)

-- R8 Axiomatization - 2(0)
r8_1 = read "{$()} | P" :: Consequence
r8Axiomatization = [r8_1]
r8Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList r8Axiomatization)

-- R11 Axiomatization - 2(0, 1)
r11_1 = read "{} | .()" :: Consequence
r11Axiomatization = r8Axiomatization ++ [r11_1]
r11Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList r11Axiomatization)

-- R13 Axiomatization - 2(\lnot, 0)
r13_1 = read "{} | -($())" :: Consequence
r13Axiomatization = r4Axiomatization ++ [r13_1]
r13Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList r13Axiomatization)

-- S2 Axiomatization - 2(v)
s2_1 = read "{P} | +(P, Q)" :: Consequence
s2_2 = read "{+(P, P)} | P" :: Consequence
s2_3 = read "{+(P, Q)} | +(Q, P)" :: Consequence
s2_4 = read "{+(P, +(Q, R))} | +(+(P, Q), R)" :: Consequence
s2Axiomatization = [s2_1, s2_2, s2_3, s2_4]
s2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList s2Axiomatization)

-- S4 Axiomatization - 2(v, 1)
s4_0 = read "{} | .()" :: Consequence
s4Axiomatization = s4_0 : s2Axiomatization
s4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList s4Axiomatization)

-- S5 Axiomatization - 2(v, 0)
s5_0 = read "{+(P, $())} | P" :: Consequence
s5Axiomatization = s5_0 : s2Axiomatization
s5Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList s5Axiomatization)

-- S6 Axiomatization - 2(v, 0, 1)
s6_0 = read "{} | .()" :: Consequence
s6Axiomatization = s6_0 : s5Axiomatization
s6Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList s6Axiomatization)

-- P2 Axiomatization - 2(^)
p2_1 = read "{P, Q} | *(P, Q)" :: Consequence
p2_2 = read "{*(P, Q)} | P" :: Consequence
p2_3 = read "{*(P, Q)} | Q" :: Consequence
p2Axiomatization = [p2_1, p2_2, p2_3]
p2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList p2Axiomatization)

-- P4 Axiomatization - 2(^, 0)
p4_0 = read "{$()} | P" :: Consequence
p4Axiomatization = p4_0 : p2Axiomatization
p4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList p4Axiomatization)

-- P5 Axiomatization - 2(^, 1)
p5_0 = read "{} | .()" :: Consequence
p5Axiomatization = p5_0 : p2Axiomatization
p5Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList p5Axiomatization)

-- P6 Axiomatization - 2(^, 0, 1)
p6_0 = read "{} | .()" :: Consequence
p6Axiomatization = p6_0 : p4Axiomatization
p6Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList p6Axiomatization)

-- A4 Axiomatization - 2(v, ^)
a4_5 = read "{+(R, P), +(R, Q)} | +(R, *(P, Q))" :: Consequence
a4_6 = read "{+(R, *(P, Q))} | +(R, P)" :: Consequence
a4_7 = read "{+(R, *(P, Q))} | +(R, Q)" :: Consequence
a4Axiomatization = s2Axiomatization ++ [a4_5, a4_6, a4_7]
a4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList a4Axiomatization)

-- A2 Axiomatization - 2(v, ^, 1)
a2_0 = read "{} | .()" :: Consequence
a2Axiomatization = a2_0 : a4Axiomatization
a2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList a2Axiomatization)

-- A3 Axiomatization - 2(v, ^, 0)
a3Axiomatization = p2Axiomatization ++ s5Axiomatization
a3Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList a3Axiomatization)

-- A1 Axiomatization - 2(v, ^, 0, 1)
a1_0 = read "{} | .()" :: Consequence
a1Axiomatization = a1_0 : a3Axiomatization
a1Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList a1Axiomatization)

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
f7_0 = read "{+*(A, P, $())} | +*(A, P, Q)" :: Consequence

f7Axiomatization = f6Axiomatization ++ [f7_0]
f7Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f7Axiomatization)

-- F_8^\inf Axiomatization - 2(ki,0)
f8_0 = read "{>*(A, P, $())} | >*(A, P, Q)" :: Consequence

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

-- F_4^\inf Axiomatization - 2(ad, 1)
f4_1 = read "{} | .()" :: Consequence

f4Axiomatization = f1Axiomatization ++ [f4_1]
f4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f4Axiomatization)

-- F_2^\inf Axiomatization - 2(ak)
f2_1 = read "{P} | *+(Q, P, P)" :: Consequence
f2_2 = read "{*+(P, P, P)} | P" :: Consequence
f2_3 = read "{*+(Q, P, P)} | *+(P, Q, Q)" :: Consequence
f2_4 = read "{*+(*+(R, Q, Q), P, P)} | *+(R, *+(Q, P, P), *+(Q, P, P))" :: Consequence
f2_5 = read "{*+(*+(R, P, P), S, S), *+(*+(R, Q, Q), S, S)} | *+(*+(R, P, Q), S, S)" :: Consequence
f2_6 = read "{*+(*+(R, P, Q), S, S)} | *+(*+(R, P, P), S, S)" :: Consequence
f2_7 = read "{*+(*+(R, P, Q), S, S)} | *+(*+(R, Q, Q), S, S)" :: Consequence

f2Axiomatization = [f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7]
f2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f2Axiomatization)

-- F_3^\inf Axiomatization - 2(ak, 1)
f3_8 = read "{} | .()" :: Consequence

f3Axiomatization = f2Axiomatization ++ [f3_8]
f3Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList f3Axiomatization)

-- L_4 Axiomatization - 2(+_3)
l4_1 = read "{P, Q, R} | ++(P, Q, R)" :: Consequence
l4_2 = read "{++(P, Q, R)} | ++(Q, P, R)" :: Consequence
l4_3 = read "{++(P, Q, R)} | ++(P, R, Q)" :: Consequence
l4_4 = read "{P} | ++(P, Q, Q)" :: Consequence
l4_5 = read "{++(P, Q, Q)} | P" :: Consequence
l4_6 = read "{++(P, Q, ++(R, S, T))} | ++(++(P, Q, R), S, T)" :: Consequence

l4Axiomatization = [l4_1, l4_2, l4_3, l4_4, l4_5, l4_6]
l4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList l4Axiomatization)

-- L_2 Axiomatization - 2(+_3, 1)
l2_7 = read "{} | .()" :: Consequence

l2Axiomatization = l4Axiomatization ++ [l2_7]
l2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList l2Axiomatization)

-- L_3 Axiomatization - 2(+_3, 0)
l3_7 = read "{$()} | P" :: Consequence

l3Axiomatization = l4Axiomatization ++ [l3_7]
l3Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList l3Axiomatization)

-- L_5 Axiomatization - 2(+_3, \lnot)
l5_7 = read "{P, -(P)} | Q" :: Consequence
l5_8 = read "{P} | -(-(P))" :: Consequence
l5_9 = read "{-(-(P))} | P" :: Consequence
l5_10 = read "{-(++(P, Q, R))} | ++(-(P), Q, R)" :: Consequence
l5_11 = read "{++(-(P), Q, R)} | -(++(P, Q, R))" :: Consequence

l5Axiomatization = l4Axiomatization ++ [l5_7, l5_8, l5_9, l5_10, l5_11]
l5Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList l5Axiomatization)

-- L_1 Axiomatization - 2(+_3, 0, 1)
l1Axiomatization = l4Axiomatization ++ [l2_7, l3_7]
l1Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList l1Axiomatization)

-- D_2 Axiomatization - 2(d)
d2_1 = read "{P, Q} | >(P, Q, R)" :: Consequence
d2_2 = read "{>(Q, P, P)} | P" :: Consequence
d2_3 = read "{P} | >(Q, P, P)" :: Consequence
d2_4 = read "{>(S, T, >(P, Q, R))} | >(T, S, >(Q, P, R))" :: Consequence
d2_5 = read "{>(S, T, >(P, Q, R))} | >(T, S, >(P, R, Q))" :: Consequence
d2_6 = read "{>(A, B, >(P, Q, >(R, S, T)))} | >(A, B, >(>(P, Q, R), >(P, Q, S), T))" :: Consequence
d2_7 = read "{>(A, B, >(>(P, Q, R), >(P, Q, S), T))} | >(A, B, >(P, Q, >(R, S, T)))" :: Consequence

d2Axiomatization = [d2_1, d2_2, d2_3, d2_4, d2_5, d2_6, d2_7]
d2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList d2Axiomatization)

-- D_3 Axiomatization - 2(d, \lnot)
d3_8 = read "{>(R, S, >(Q, P, -(P)))} | >(R, S, Q)" :: Consequence
d3_9 = read "{>(R, S, Q)} | >(R, S, >(Q, P, -(P)))" :: Consequence

d3Axiomatization = d2Axiomatization ++ [d3_8, d3_9]
d3Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList d3Axiomatization)

-- D_1 Axiomatization - 2(d, +_3)
d1_0 = read "{>(P, Q, ++(R, S, T))} | ++(>(P, Q, R), >(P, Q, S), >(P, Q, T))" :: Consequence
d1_1 = read "{++(>(P, Q, R), >(P, Q, S), >(P, Q, T))} | >(P, Q, ++(R, S, T))" :: Consequence
d1_2 = read "{++(P, Q, >(R, S, T))} | >(++(P, Q, R), ++(P, Q, S), ++(P, Q, T))" :: Consequence
d1_3 = read "{>(++(P, Q, R), ++(P, Q, S), ++(P, Q, T))} | ++(P, Q, >(R, S, T))" :: Consequence
d1_4 = read "{++(A, B, >(P, Q, ++(R, S, T)))} | ++(A, B, ++(>(P, Q, R), >(P, Q, S), >(P, Q, T)))" :: Consequence
d1_5 = read "{++(A, B, ++(>(P, Q, R), >(P, Q, S), >(P, Q, T)))} | ++(A, B, >(P, Q, ++(R, S, T)))" :: Consequence
d1_6 = read "{>(A, B, ++(P, Q, >(R, S, T)))} | >(A, B, >(++(P, Q, R), ++(P, Q, S), ++(P, Q, T)))" :: Consequence
d1_7 = read "{>(A, B, >(++(P, Q, R), ++(P, Q, S), ++(P, Q, T)))} | >(A, B, ++(P, Q, >(R, S, T)))" :: Consequence

d1Axiomatization = d2Axiomatization ++ l4Axiomatization ++ [d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6, d1_7]
d1Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList d1Axiomatization)

-- C_4 Axiomatization - 2(ki, v)
c4_0 = read "{>*(P, Q, +(A, B))} | >*(P, Q, >*(+(A, B), >*(+(A, B), A, R), >*(+(A, B), >*(+(A, B), B, R), R)))" :: Consequence
c4_1 = read "{>*(P, Q, A)} | >*(P, Q, +(A, B))" :: Consequence
c4_2 = read "{>*(P, Q, B)} | >*(P, Q, +(A, B))" :: Consequence

c4Axiomatization = f5Axiomatization ++ [c4_0, c4_1, c4_2]
c4Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList c4Axiomatization)

-- C_3 Axiomatization - 2(ki, v, 0)
c3Axiomatization = c4Axiomatization ++ [f8_0]
c3Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList c3Axiomatization)

-- C_2 Axiomatization - 2(ki, v, 1)
c2Axiomatization = c4Axiomatization ++ [r6_1]
c2Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList c2Axiomatization)

-- C_1 Axiomatization - 2(ki, v, 0, 1)
c1Axiomatization = c3Axiomatization ++ [r6_1]
c1Signature = fromRight M.empty $ sigmaFromConseqRelation (S.fromList c1Axiomatization)

comb :: Int -> [a] -> [[a]]
comb 0 _      = [[]]
comb _ []     = []
comb m (x:xs) = map (x:) (comb (m-1) xs) ++ comb m xs

alphabet = ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O"]

clausulesDM :: Int -> [[String]]
clausulesDM m = comb m $ take (m + 1) alphabet

dmFormula :: Int -> String
dmFormula m = replicate (m - 1) '>' ++ "(" ++ (foldr1 (++) $ L.intersperse ", " $ take (m + 1) alphabet) ++ ")" 

lorToAk :: [String] -> String
lorToAk (c:d:[]) = fst ak ++ "(" ++ c ++ ", " ++ d ++ ", " ++ d ++ ")"
lorToAk (c:cs) = fst ak ++ "(" ++  c ++ ", " ++ aux ++ ", " ++ aux ++ ")"
    where aux = lorToAk cs

f2ExpansionAxiomatization :: Int -> [Consequence]
f2ExpansionAxiomatization m = f2Axiomatization ++ (f2ExpansionAxiomatization0 m):[f2ExpansionAxiomatizationK m k | k <- [1..clausulesLength]]
    where clausulesLength = length $ clausulesDM m

f2ExpansionAxiomatization0 :: Int -> Consequence
f2ExpansionAxiomatization0 m = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        clausules = clausulesDM m
        premisse = foldr1 (++) $ L.intersperse ", " $ map lorToAk ["S":clausule | clausule <- clausules]
        conclusion = lorToAk ["S", dmFormula m]

f2ExpansionAxiomatizationK :: Int -> Int -> Consequence
f2ExpansionAxiomatizationK m k = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        clausule = clausulesDM m !! (k -1)
        premisse = lorToAk ["S", dmFormula m]
        conclusion = lorToAk ("S":clausule)

f3ExpansionAxiomatization :: Int -> [Consequence]
f3ExpansionAxiomatization = (:) r6_1 . f2ExpansionAxiomatization

lorToAd :: [String] -> String
lorToAd (a:b:[]) = fst ad ++ "(" ++ a ++ ", " ++ b ++ ", " ++ a ++ ")"
lorToAd (a:cs) = fst ad ++ "(" ++ a ++ ", " ++ aux ++ ", " ++ a ++ ")"
    where aux = lorToAd cs

adExpansionAux :: String -> String -> [String] -> String
adExpansionAux p q (a:[]) = fst ad ++ "(" ++ p ++ ", " ++ a ++ ", " ++ q ++ ")"
adExpansionAux p q (a:cs) = fst ad ++ "(" ++ p ++ ", " ++ a ++ ", " ++ aux ++ ")"
    where aux = adExpansionAux p q cs

f1ExpansionAxiomatization :: Int -> [Consequence]
f1ExpansionAxiomatization m = f1Axiomatization ++ (f1ExpansionAxiomatization0 m):[f1ExpansionAxiomatizationK m k | k <- [1..clausulesLength]]
    where clausulesLength = length $ clausulesDM m

f1ExpansionAxiomatization0 :: Int -> Consequence
f1ExpansionAxiomatization0 m = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        (firstClausule:clausules) = clausulesDM m
        premisse = fst ad ++ "(" ++ "T," ++ "S," ++ lorToAd firstClausule ++ ")"
        conclusion = fst ad ++ "(" ++ "T," ++ "S," ++ adExpansionAux (lorToAd firstClausule) (dmFormula m) (map lorToAd clausules) ++ ")"

f1ExpansionAxiomatizationK :: Int -> Int -> Consequence
f1ExpansionAxiomatizationK m k = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        clausule = clausulesDM m !! (k - 1)
        premisse = fst ad ++ "(" ++ "T," ++ "S," ++ dmFormula m ++ ")"
        conclusion = fst ad ++ "(" ++ "T," ++ "S," ++ lorToAd clausule ++ ")"

f4ExpansionAxiomatization :: Int -> [Consequence]
f4ExpansionAxiomatization = (:) r6_1 . f1ExpansionAxiomatization

landToKi :: [String] -> String
landToKi (a:b:[]) = fst ki ++ "(" ++ a ++ ", " ++ a ++ ", " ++ b ++ ")"
landToKi (a:cs) = fst ki ++ "(" ++ a ++ ", " ++ a ++ ", " ++ aux ++ ")"
    where aux = landToKi cs

kiExpansionAux :: String -> String -> [String] -> String
kiExpansionAux q r (a:[]) = fst ki ++ "(" ++ q ++ ", " ++ (fst ki ++ "(" ++ q ++ ", " ++ a ++ ", " ++ r ++ ")") ++ ", " ++ r ++ ")"
kiExpansionAux q r (a:cs) = fst ki ++ "(" ++ q ++ ", " ++ (fst ki ++ "(" ++ q ++ ", " ++ a ++ ", " ++ r ++ ")") ++ ", " ++ aux ++ ")"
    where aux = kiExpansionAux q r cs

f5ExpansionAxiomatization :: Int -> [Consequence]
f5ExpansionAxiomatization m = f5Axiomatization ++ (f5ExpansionAxiomatization0 m):[f5ExpansionAxiomatizationK m k | k <- [1..clausulesLength]]
    where clausulesLength = length $ clausulesDM m

f5ExpansionAxiomatization0 :: Int -> Consequence
f5ExpansionAxiomatization0 m = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        premisse = fst ki ++ "(" ++ "T," ++ "S," ++ dmFormula m ++ ")"
        conclusion = fst ki ++ "(" ++ "T," ++ "S," ++ kiExpansionAux (dmFormula m) "R" (map landToKi $ clausulesDM m) ++ ")"

f5ExpansionAxiomatizationK :: Int -> Int -> Consequence
f5ExpansionAxiomatizationK m k = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        clausule = clausulesDM m !! (k - 1)
        premisse = fst ki ++ "(" ++ "T," ++ "S," ++ landToKi clausule ++ ")"
        conclusion = fst ki ++ "(" ++ "T," ++ "S," ++ dmFormula m ++ ")"

f8ExpansionAxiomatization :: Int -> [Consequence]
f8ExpansionAxiomatization = (:) f8_0 . f5ExpansionAxiomatization


landToKa :: [String] -> String
landToKa (a:b:[]) = fst ka ++ "(" ++ a ++ ", " ++ b ++ ", " ++ b ++ ")"
landToKa (a:cs) = fst ka ++ "(" ++ a ++ ", " ++ aux ++ ", " ++ aux ++ ")"
    where aux = landToKa cs

kaExpansionAux :: String -> [String] -> String
kaExpansionAux q (a:b:[]) = fst ka ++ "(" ++ q ++ ", " ++ a ++ ", " ++ b ++ ")"
kaExpansionAux q (a:cs) = fst ka ++ "(" ++ q ++ ", " ++ a ++ ", " ++ aux ++ ")"
    where aux = kaExpansionAux q cs

f6ExpansionAxiomatization :: Int -> [Consequence]
f6ExpansionAxiomatization m = f6Axiomatization ++ (f6ExpansionAxiomatization0 m):[f6ExpansionAxiomatizationK m k | k <- [1..clausulesLength]]
    where clausulesLength = length $ clausulesDM m

f6ExpansionAxiomatization0 :: Int -> Consequence
f6ExpansionAxiomatization0 m = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        premisse = fst ka ++ "(" ++ "T," ++ "S," ++ dmFormula m ++ ")"
        conclusion = fst ka ++ "(" ++ "T," ++ "S," ++ kaExpansionAux (dmFormula m) (map landToKa $ clausulesDM m) ++ ")"

f6ExpansionAxiomatizationK :: Int -> Int -> Consequence
f6ExpansionAxiomatizationK m k = read $ "{" ++ premisse ++ "} | " ++ conclusion :: Consequence
    where
        clausule = clausulesDM m !! (k - 1)
        premisse = fst ka ++ "(" ++ "T," ++ "S," ++ landToKa clausule ++ ")"
        conclusion = fst ka ++ "(" ++ "T," ++ "S," ++ dmFormula m ++ ")"

f7ExpansionAxiomatization :: Int -> [Consequence]
f7ExpansionAxiomatization = (:) f7_0 . f6ExpansionAxiomatization