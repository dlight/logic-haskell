module Post where

-- import Prelude hiding (and, or)
-- import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Control.Monad.Extra as ME
import Data.Either
import Data.Maybe
-- import Logic
import Signature
import NMatrix
import Control.Exception.Safe (MonadThrow)
import Axiomatization
import Logic
import Clone

valuesMatrix = (S.fromList [0, 1], S.fromList [1]) :: Values Int

r11Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [oneIdentity, zeroIdentity]}
r13Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [negation, zeroIdentity]}
r4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [negation]}
r6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [oneIdentity]}
r8Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [zeroIdentity]}
s2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [or_]}
s4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [or_, oneIdentity]}
s5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [or_, zeroIdentity]}
s6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [or_, oneIdentity, zeroIdentity]}
p2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_]}
p4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, zeroIdentity]}
p5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, oneIdentity]}
p6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, oneIdentity, zeroIdentity]}
l1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [xor, zeroIdentity, oneIdentity]}
l2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [xor, oneIdentity]}
l3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [xor, zeroIdentity]}
l4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [xor]}
l5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [xor, negation]}
f1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ad]}
f2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ak]}
f3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ak, oneIdentity]}
f4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ad, oneIdentity]}
f5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki]}
f6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ka]}
f7Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ka, zeroIdentity]}
f8Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, zeroIdentity]}
d2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [d]}
d3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [d, negation]}
d1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [d, xor]}
a4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, or_]}
a3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, or_, zeroIdentity]}
a2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, or_, oneIdentity]}
a1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [and_, or_, zeroIdentity, oneIdentity]}
c4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, or_]}
c3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, or_, zeroIdentity]}
c2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, or_, oneIdentity]}
c1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, or_, zeroIdentity, oneIdentity]}

greenMatrices = [r4Matrix,r11Matrix,r13Matrix,r6Matrix,r8Matrix,s2Matrix,s4Matrix,s5Matrix,
    s6Matrix,p2Matrix,p4Matrix,p5Matrix,p6Matrix,l1Matrix,l2Matrix,l3Matrix,l4Matrix,
    l5Matrix,f1Matrix,f2Matrix,f3Matrix,f4Matrix,f5Matrix,f6Matrix,f7Matrix,f8Matrix,
    d2Matrix,d3Matrix,d1Matrix,a4Matrix,a3Matrix,a2Matrix,a1Matrix,c4Matrix,c3Matrix,
    c2Matrix,c1Matrix]

f1ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ad, dm x]}) [2..]
f2ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ak, dm x]}) [2..]
f3ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ak, oneIdentity, dm x]}) [2..]
f4ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ad, oneIdentity, dm x]}) [2..]
f5ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, dm x]}) [2..]
f6ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ka, dm x]}) [2..]
f7ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ka, zeroIdentity, dm x]}) [2..]
f8ExpansionMatrix = map (\x -> NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation' [ki, zeroIdentity, dm x]}) [2..]


pllp :: (MonadThrow m) => NMatrix Int -> (m (NMatrix Int))
pllp baseA = case fromJust $ ME.findM (isTermEquivalent baseA) greenMatrices of
    Just baseB -> return baseB
    Nothing    -> pllpRecursive 0 baseA

pllpRecursive :: (MonadThrow m) => Int -> NMatrix Int -> (m (NMatrix Int))
pllpRecursive depth base =
    do
        let f4ExpansionM = f4ExpansionMatrix !! depth
        let f8ExpansionM = f8ExpansionMatrix !! depth
        let f3ExpansionM = f3ExpansionMatrix !! depth
        let f7ExpansionM = f7ExpansionMatrix !! depth
        let f1ExpansionM = f1ExpansionMatrix !! depth
        let f5ExpansionM = f5ExpansionMatrix !! depth
        let f2ExpansionM = f2ExpansionMatrix !! depth
        let f6ExpansionM = f6ExpansionMatrix !! depth
        isInCloneF4 <- isInClone base f4ExpansionM
        isInCloneF8 <- isInClone base f8ExpansionM
        isInCloneF3 <- isInClone base f3ExpansionM
        isInCloneF7 <- isInClone base f7ExpansionM
        isInCloneF1 <- isInClone base f1ExpansionM
        isInCloneF5 <- isInClone base f5ExpansionM
        isInCloneF2 <- isInClone base f2ExpansionM
        isInCloneF6 <- isInClone base f6ExpansionM
        if isInCloneF4 then return f4ExpansionM
        else if isInCloneF8 then return f8ExpansionM
        else if isInCloneF3 then return f3ExpansionM
        else if isInCloneF7 then return f7ExpansionM
        else if isInCloneF1 then return f1ExpansionM
        else if isInCloneF5 then return f5ExpansionM
        else if isInCloneF2 then return f2ExpansionM
        else if isInCloneF6 then return f6ExpansionM
        else pllpRecursive (depth+1) base

getAxiomatization :: NMatrix Int -> [Consequence]
getAxiomatization matrix
    | matrix == r4Matrix = r4Axiomatization -- 2(\lnot)
    | matrix == r6Matrix = r6Axiomatization -- 2(1)
    | matrix == r8Matrix = r8Axiomatization -- 2(0)
    | matrix == r11Matrix = r11Axiomatization -- 2(0,1)
    | matrix == r13Matrix = r13Axiomatization -- 2(\lnot,0)
    | matrix == s2Matrix = s2Axiomatization -- 2(v)
    | matrix == s4Matrix = s4Axiomatization -- 2(v,1)
    | matrix == s5Matrix = s5Axiomatization -- 2(v,0)
    | matrix == s6Matrix = s6Axiomatization -- 2(v,0,1)
    | matrix == p2Matrix = p2Axiomatization -- 2(^)
    | matrix == p4Matrix = p4Axiomatization -- 2(^,0)
    | matrix == p5Matrix = p5Axiomatization -- 2(^,1)
    | matrix == p6Matrix = p6Axiomatization -- 2(^,0,1)
    | matrix == l4Matrix = l4Axiomatization -- 2(+_3)
    | matrix == l2Matrix = l2Axiomatization -- 2(+_3,1)
    | matrix == l3Matrix = l3Axiomatization -- 2(+_3,0)
    | matrix == l5Matrix = l5Axiomatization -- 2(+_3,\lnot)
    | matrix == l1Matrix = l1Axiomatization -- 2(+_3,0,1)
    | matrix == f6Matrix = f6Axiomatization -- 2(ka)
    | matrix == f5Matrix = f5Axiomatization -- 2(ki)
    | matrix == f7Matrix = f7Axiomatization -- 2(ka,0)
    | matrix == f8Matrix = f8Axiomatization -- 2(ki,0)
    | matrix == f1Matrix = f1Axiomatization -- 2(ad)
    | matrix == f4Matrix = f4Axiomatization -- 2(ad,1)
    | matrix == f2Matrix = f2Axiomatization -- 2(ak)
    | matrix == f3Matrix = f3Axiomatization -- 2(ak,1)
    | matrix == d2Matrix = d2Axiomatization -- 2(d)
    | matrix == d3Matrix = d3Axiomatization -- 2(d,\lnot)
    | matrix == d1Matrix = d1Axiomatization -- 2(d,+_3)
    | matrix == a4Matrix = a4Axiomatization -- 2(v,^)
    | matrix == a3Matrix = a3Axiomatization -- 2(v,^,0)
    | matrix == a2Matrix = a2Axiomatization -- 2(v,^,1)
    | matrix == a1Matrix = a1Axiomatization -- 2(v,^,0,1)
    | matrix == c4Matrix = c4Axiomatization -- 2(ki,v)
    | matrix == c3Matrix = c3Axiomatization -- 2(ki,v,0)
    | matrix == c2Matrix = c2Axiomatization -- 2(ki,v,1)
    | matrix == c1Matrix = c1Axiomatization -- 2(ki,v,0,1)
    | otherwise          = getAxiomatizationRecursive 0 matrix


getAxiomatizationRecursive :: Int -> NMatrix Int -> [Consequence]
getAxiomatizationRecursive depth matrix
    | matrix == f4ExpansionMatrix !! depth = f4ExpansionAxiomatization $ depth + 2
    | matrix == f8ExpansionMatrix !! depth = f8ExpansionAxiomatization $ depth + 2
    | matrix == f3ExpansionMatrix !! depth = f3ExpansionAxiomatization $ depth + 2
    | matrix == f7ExpansionMatrix !! depth = f7ExpansionAxiomatization $ depth + 2
    | matrix == f1ExpansionMatrix !! depth = f1ExpansionAxiomatization $ depth + 2
    | matrix == f5ExpansionMatrix !! depth = f5ExpansionAxiomatization $ depth + 2
    | matrix == f2ExpansionMatrix !! depth = f2ExpansionAxiomatization $ depth + 2
    | matrix == f6ExpansionMatrix !! depth = f6ExpansionAxiomatization $ depth + 2
    | otherwise                            = getAxiomatizationRecursive (depth+1) matrix