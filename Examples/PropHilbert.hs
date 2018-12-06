module Examples.PropHilbert where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Logic
import NMatrix
import Signature
import Control.Exception.Safe (SomeException)
import Data.Either
import Formula
import Semantics

ax1 = read "{} | ==>(a, ==>(b, a))" :: Consequence
ax2 = read "{} | ==>(==>(a, ==>(b, c)), ==>(==>(a, b), ==>(a,c)))" :: Consequence
ax3 = read "{} | ==>(==>(-(b),-(a)), ==>(==>(-(b), a), b))" :: Consequence
mp  = read "{==>(a, b), a} | b" :: Consequence

consequences = [ax1, ax2, ax3, mp]

signature = sigmaFromConseqRelation (S.fromList consequences) :: Either SomeException Signature

rightSignature = fromRight M.empty signature

logic = makeLogic rightSignature consequences :: Either SomeException Logic

impliesTruthTable = mkTruthTable [([0, 0], 1),
                                  ([0, 1], 1),
                                  ([1, 1], 1),
                                  ([1, 0], 0)] :: Either SomeException (TruthTable Int)

negationTruthTable = mkTruthTable [([0], 1),
                                   ([1], 0)] :: Either SomeException (TruthTable Int)

implies = ("==>", fromRight M.empty impliesTruthTable)
negation = ("-", fromRight M.empty negationTruthTable)

emptyLogicInstance = emptyLogic M.empty
rightLogic = fromRight emptyLogicInstance logic

valuesMatrix = (S.fromList [0, 1], S.fromList [1])
sampleInterpretation = mkInterpretation (sigma rightLogic) [implies, negation] 
                    :: Either SomeException (Interpretation Int)

rightInterpretation = fromRight M.empty sampleInterpretation

matrix = NMatrix {values = valuesMatrix, interpretation = rightInterpretation}

sampleFormula = read "==>(a, ==>(b, a))" :: Formula

-- for a given logic, test if sampleFormula is a tautology
testTautology = isFormulaTautology rightLogic matrix sampleFormula :: Either SomeException Bool

testFormulaValid = isFormulaValid matrix sampleFormula :: Either SomeException Bool
--sampleValuation = M.fromList [("a", 1), ("b", 0)] :: Valuation Int
--sampleEval = evaluate (fromRight M.empty sampleInterpretation) sampleValuation sampleFormula

sampleValues = (S.fromList [0,1], S.fromList[1])

sampleNmatrices = generateNMatrices rightSignature sampleValues :: Either SomeException [NMatrix Int]

rightNmatrices = fromRight [] sampleNmatrices
