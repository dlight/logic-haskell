{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Formula where

import Text.Read
--import Signature
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as DMaybe
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Data.Aeson.Types (ToJSON, FromJSON)
import GHC.Generics (Generic)

type Symbol = String

type Variable = String

-- | A well-formed formula
-- Example:
-- ==>(a, ==>(b, a))
data Formula = 
    Var String | 
    Op Symbol [Formula]
    deriving (Show, Eq, Ord, Generic, ToJSON, FromJSON)

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

varsFromFormula :: Formula -> [Formula]
varsFromFormula v@(Var x) = [v]
varsFromFormula (Op _ fmlas) = foldr (++) [] (map varsFromFormula fmlas)

-- | Compute the arity of a formula
getFormulaArity :: Formula -> Int
getFormulaArity = length . varsFromFormula
    --case varsFromFormula fmla of
    --    Left e -> throwM e
    --    Right (_, vars) -> return $ S.size vars

substitution :: Variable -> Formula -> Formula -> Formula
substitution v f f'@(Var s) = if v == s then f else f'
substituiion v f (Op s fs) = Op s (map (substitution v f) fs)

-- | Given an arity, a maximum new arity, and a list of variables, produce tuples of these variables
-- to be applied in a connective of that arity
makeVariablesPermsUpToIso :: Int -> Int -> S.Set [Formula]
makeVariablesPermsUpToIso originalArity maximumNewArity = 
        S.unions $ makeNonRepeatedPermutations <$> [1..maximumNewArity]
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
    return $ foldr ((:) . mkSubsFromSets varList) [] source
    where
        varList = varsFromFormula target
        mkSubsFromSets :: [Formula] -> [Formula] -> Substitution
        mkSubsFromSets varList = M.fromList . zip varList

    --case varsFromFormula target of
    --    Left e -> throwM e
    --    Right (_, vars) -> return $ foldr ((:) . mkSubsFromSets varList) [] source
    --        where
    --            varList = S.toList $ S.map Var vars
    --            mkSubsFromSets :: [Formula] -> [Formula] -> Substitution
    --            mkSubsFromSets varList = M.fromList . zip varList

-- | Apply a substitution in a formula
applySubstitution :: Substitution -> Formula -> Formula
applySubstitution subs v@(Var s) = DMaybe.fromMaybe v ((M.!?) subs v)
applySubstitution subs fmla@(Op symb ops) = 
    DMaybe.fromMaybe (Op symb (applySubstitutionLeaves subs <$> ops)) ((M.!?) subs fmla)

-- | Apply a substitution only in the leaves of a formula
applySubstitutionLeaves :: Substitution -> Formula -> Formula
applySubstitutionLeaves subs v@(Var s) = DMaybe.fromMaybe v ((M.!?) subs v)
applySubstitutionLeaves subs fmla@(Op symb ops) = Op symb (applySubstitutionLeaves subs <$> ops)

-- | Given a derived connective (a formula), a maximum projections arity and
-- produces all the derived connectives
-- induced com multiple finitarily composing it with all possible projections
-- of smaller or equal arity.
makeDerivedFromProjections :: (MonadThrow m) => Formula -> Int -> m [Formula]
makeDerivedFromProjections fmla maximumProjArity = 
    --case getFormulaArity fmla of
    --    Left e -> throwM e
    --    Right n ->
    case makeSubstitutions fmla (makeVariablesPermsUpToIso (getFormulaArity fmla) maximumProjArity) of
        Left e -> throwM e
        Right subs -> 
            return $ flip applySubstitutionLeaves fmla <$> subs


