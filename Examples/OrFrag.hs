module Examples.OrFrag where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Logic
import NMatrix
import Signature
import Control.Exception.Safe (SomeException)
import Data.Either
import Formula
import Semantics

ax1 = read "{a} | +(a, b)" :: Consequence
ax2 = read "{+(a, a)} | a" :: Consequence
ax3 = read "{+(a, b)} | +(b, a)" :: Consequence
ax4 = read "{+(a, +(b, c))} | +(+(a, b), c)" :: Consequence

consequences = [ax1, ax2, ax3, ax4]

signature = sigmaFromConseqRelation(S.fromList consequences) :: Either SomeException Signature
rightSignature = fromRight M.empty signature

values = (S.fromList [0,1], S.fromList [1]) :: Values Int

orTruthTable = mkTruthTable [([0, 0], 0),
                             ([0, 1], 1),
                             ([1, 1], 1),
                             ([1, 0], 1)] :: Either SomeException (TruthTable Int)

orconn = ("+", fromRight M.empty orTruthTable)

logic = makeLogic rightSignature consequences :: Either SomeException Logic

emptyLogicInstance = emptyLogic M.empty
rightLogic = fromRight emptyLogicInstance logic

sampleInterpretation = mkInterpretation (sigma rightLogic) [orconn] 
                    :: Either SomeException (Interpretation Int)

rightInterpretation = fromRight M.empty sampleInterpretation

matrix = NMatrix {NMatrix.values = Examples.OrFrag.values, interpretation = rightInterpretation}

sampleFormula = read "+(a,a)" :: Formula
-- test validity
formulaValid = isFormulaValid' matrix sampleFormula :: Either SomeException [Valuation Int]
-- test consequence
sampleValuation = M.fromList [("a", 0), ("b", 0)]
conseqSatisf = isConsequenceSatisfied' matrix sampleValuation ax1 :: Either SomeException [Formula]
-- test consequence valid
conseqValid = isConsequenceValid' matrix ax1 :: Either SomeException [(Valuation Int, [Formula])]

sub = S.fromList [ax4]

indep = checkIndependence' Examples.OrFrag.values (S.fromList consequences) sub :: Either SomeException [(NMatrix Int, [(Valuation Int, [(Consequence, [Formula])])])]
rightIndep = fromRight [] indep


indep' = checkIndependence Examples.OrFrag.values (S.fromList consequences) sub :: Either SomeException Bool

ttderived = truthTableFromDerived (read "+(a, +(b, b))") matrix :: Either SomeException (TruthTable Int)

