module Post where

-- import Prelude hiding (and, or)
-- import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Either
-- import Data.Maybe
-- import Logic
-- import Signature
import NMatrix
-- import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Axiomatization

valuesMatrix = (S.fromList [0, 1], S.fromList [1]) :: Values Int

r4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation r4Signature [negation]}
r6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation r6Signature [one]}
r8Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation r8Signature [zero]}
r11Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation r11Signature [one, zero]}
r13Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation r13Signature [negation, zero]}
s2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation s2Signature [or_]}
s4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation s4Signature [or_, one]}
s5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation s5Signature [or_, zero]}
s6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation s6Signature [or_, one, zero]}
p2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation p2Signature [and_]}
p4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation p4Signature [and_, zero]}
p5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation p5Signature [and_, one]}
p6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation p6Signature [and_, one, zero]}
l1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation l1Signature [xor, zero, one]}
l2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation l2Signature [xor, one]}
l3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation l3Signature [xor, zero]}
l4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation l4Signature [xor]}
l5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation l5Signature [xor, negation]}
f1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f1Signature [ad]}
f2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f2Signature [ak]}
f3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f3Signature [ak, one]}
f4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f4Signature [ad, one]}
f5Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f5Signature [ki]}
f6Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f6Signature [ka]}
f7Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f7Signature [ka, zero]}
f8Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation f8Signature [ki, zero]}
d2Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation d2Signature [d]}
d3Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation d3Signature [d, negation]}
d1Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation d1Signature [d, xor]}
a4Matrix = NMatrix {values = valuesMatrix, interpretation = fromRight M.empty $ mkInterpretation a4Signature [and_, or_]}
