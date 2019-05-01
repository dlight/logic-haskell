{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Formula where

import Text.Read
import Signature
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as DMaybe
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Data.Aeson.Types (ToJSON)
import GHC.Generics (Generic)

type Symbol = String

type Variable = String

-- | A well-formed formula
-- Example:
-- ==>(a, ==>(b, a))
data Formula = 
    Var String | 
    Op Symbol [Formula]
    deriving (Show, Eq, Ord, Generic, ToJSON)

type Substitution = M.Map Formula Formula 

-- | Parser for formulas
instance Read Formula where
    readPrec = 
                    prec up_prec $ do
                        Symbol op <- lexP
                        Punc "(" <- lexP
                        xs <- readListPrec
                        Punc ")" <- lexP
                        return (Op op xs)
                    +++
                    do
                        prec app_prec $ do
                            do
                                Symbol op <- lexP
                                Punc "(" <- lexP
                                Punc ")" <- lexP
                                return $ Op op []
                            +++
                            do
                                Ident i <- lexP
                                return $ Var i
                where   app_prec = 10
                        up_prec = 5
    readListPrec = do
                f <- readPrec
                do
                    do
                        Punc "," <- lexP
                        fs <- readListPrec 
                        return (f : fs)
                    +++
                        return [f]


-- | Extract the signature induced by a formula
sigmaFromFormula :: (MonadThrow m) => Formula -> m Signature
sigmaFromFormula f = fst <$> sigmaVarsFromFormula f

-- | Extract the signature induced by a formula
sigmaVarsFromFormula :: (MonadThrow m) => Formula -> m (Signature, S.Set Variable)
sigmaVarsFromFormula (Var x) = return (M.empty, S.fromList [x])
sigmaVarsFromFormula (Op op fs) = 
    do
        conn <- mkConnective (op, length fs)
        (sigmaFromArgs, varsFromArgs) <- foldr f (return (M.empty, S.empty)) fs
        return (M.unionWith S.union (M.fromList [(length fs, S.fromList [conn])]) sigmaFromArgs, varsFromArgs)
            where f formula msigma = do
                                        (sff, vars) <- sigmaVarsFromFormula formula
                                        (sigma, vars') <- msigma
                                        return (M.unionWith S.union sigma sff, S.union vars vars')

-- | Compute the arity of a formula
getFormulaArity :: (MonadThrow m) => Formula -> m Int
getFormulaArity fmla = 
    case sigmaVarsFromFormula fmla of
        Left e -> throwM e
        Right (_, vars) -> return $ S.size vars

substitution :: Variable -> Formula -> Formula -> Formula
substitution v f f'@(Var s) = if v == s then f else f'
substituiion v f (Op s fs) = Op s (map (substitution v f) fs)

translation :: (MonadThrow m) => ([Formula] -> Connective -> Formula) -> Formula -> m Formula
translation _ f@(Var s) = pure f
translation t (Op s' fs) = flip t <$> mkConnective (s',(length fs)) <*> mapM (translation t) fs

-- | Given an arity and a list of variables, produce tuples of these variables
-- to be applied in a connective of that arity
makeVariablesPermsUpToIso :: Int -> S.Set [Formula]
makeVariablesPermsUpToIso originalArity = 
        S.unions $ makeNonRepeatedPermutations <$> [1..originalArity]
    where
        makeNonRepeatedPermutations = S.fromList . L.permutations . makeVarSet originalArity
        makeVarSet originalArity currentArity = 
            replicate nrep1 (Var "p1") ++ map (Var . ("p"++) . show) [2..currentArity]
                where 
                    nrep1 = originalArity - currentArity + 1
                    unrep = originalArity - nrep1    

-- | Produce substitutions from a Formula
-- 1. extract the variable set of a formula, and infer its arity from it
-- 2. produce substitutions given the variables and a set of formulas
-- example: makeSubstitutions "+(A,B)" "{["B", "A"],["A","A"]}"
makeSubstitutions :: (MonadThrow m) => Formula -> S.Set [Formula] -> m [Substitution]
makeSubstitutions target source = 
    case sigmaVarsFromFormula target of
        Left e -> throwM e
        Right (_, vars) -> return $ foldr ((:) . mkSubsFromSets varList) [] source
            where
                varList = S.toList $ S.map Var vars
                mkSubsFromSets :: [Formula] -> [Formula] -> Substitution
                mkSubsFromSets varList = M.fromList . zip varList

-- | Apply a substitution in a formula
applySubstitution :: Substitution -> Formula -> Formula
applySubstitution subs v@(Var s) = DMaybe.fromMaybe v ((M.!?) subs v)
applySubstitution subs fmla@(Op symb ops) = 
    DMaybe.fromMaybe (Op symb (applySubstitutionLeaves subs <$> ops)) ((M.!?) subs fmla)

-- | Apply a substitution only in the leaves of a formula
applySubstitutionLeaves :: Substitution -> Formula -> Formula
applySubstitutionLeaves subs v@(Var s) = DMaybe.fromMaybe v ((M.!?) subs v)
applySubstitutionLeaves subs fmla@(Op symb ops) = Op symb (applySubstitutionLeaves subs <$> ops)

-- | Given a derived connective (a formula), produces all the derived connectives
-- induced com multiple finitarily composing it with all possible projections
-- of smaller or equal arity.
makeDerivedFromProjections :: (MonadThrow m) => Formula -> m [Formula]
makeDerivedFromProjections fmla = 
    case getFormulaArity fmla of
        Left e -> throwM e
        Right n ->
            case makeSubstitutions fmla (makeVariablesPermsUpToIso n) of
                Left e -> throwM e
                Right subs -> 
                    return $ flip applySubstitutionLeaves fmla <$> subs


