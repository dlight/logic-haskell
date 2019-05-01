{-# LANGUAGE ScopedTypeVariables #-}

module Semantics where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe
import Logic
import Formula
import NMatrix
import Signature
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Control.Monad (replicateM, mapM, sequence, liftM, filterM)
import Control.Monad.Loops
import Connective
import qualified Data.List as L

-- | Assign to each variable a value
type Valuation a = M.Map Variable a

-- | Exceptions for evaluation time
data EvaluationException = 
    NoVariableAssignment String | 
    NoConnectiveInterpretation Connective |
    NoArgumentMatching [String]
    deriving (Show, Eq)
instance Exception EvaluationException

-- | Evaluate a formula given an interpretation
evaluate :: (MonadThrow m, Show a, Ord a) => Interpretation a -> Valuation a -> Formula -> m a
evaluate _ valuation (Var x) = case valuation M.!? x of
                                    Nothing -> throwM $ NoVariableAssignment x
                                    Just v -> return v
evaluate interpret valuation (Op symb forms) = 
    do 
        conn <- mkConnective (symb, length forms)
        case interpret M.!? conn of
            Nothing -> throwM $ NoConnectiveInterpretation conn
            Just truthtable ->  
                do
                    evals <- mapM (evaluate interpret valuation) forms
                    case truthtable M.!? evals of
                        Nothing -> throwM $ NoArgumentMatching (map show forms)
                        Just v -> return v

-- | Check the satisfiability of a formula given a NMatrix and a valuation
isFormulaSatisfied :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Valuation a -> Formula -> m Bool
isFormulaSatisfied nmatrix valuation formula = 
    case evaluate interp valuation formula of
        Left e -> throwM e
        Right v -> return $ v `S.member` designated
    where   
        interp = NMatrix.interpretation nmatrix
        designated = (snd . values) nmatrix

-- | Check the validity of a formula given a NMatrix, checking all possible valuations
isFormulaValid :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Formula -> m Bool
isFormulaValid nmatrix formula = null <$> isFormulaValid' nmatrix formula

-- | Check the validity of a formula given a NMatrix, return the first valuation in case of fail
isFormulaValid' :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Formula -> m [Valuation a]
isFormulaValid' nmatrix formula = 
        case sigmaVarsFromFormula formula of
            Left e -> throwM e
            Right (_, vars) ->
                    filterM f (generateValuations (S.toList vars) values)
                        where
                            f = fmap not . flip (isFormulaSatisfied nmatrix) formula
                            values = (S.toList . fst . NMatrix.values) nmatrix

-- | Check the satisfitibility of a consequence given an NMatrix and a valuation
isConsequenceSatisfied :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Valuation a -> Consequence -> m Bool
isConsequenceSatisfied nmatrix valuation conseq = null <$> isConsequenceSatisfied' nmatrix valuation conseq

-- | Check the satisfitibility of a consequence given an NMatrix and a valuation
-- Nothing means satisfiability
isConsequenceSatisfied' :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Valuation a -> Consequence -> m [Formula]
isConsequenceSatisfied' nmatrix valuation conseq = 
        case filterM (fmap not . isFormulaSatisfied nmatrix valuation) (S.toList $ predecessors conseq) of
            Left e -> throwM e
            Right [] -> case conclusionSatisfied of
                            Left e -> throwM e
                            Right True -> return []
                            Right False -> return [consequence conseq]
            Right ls -> return []
            where
                conclusionSatisfied = isFormulaSatisfied nmatrix valuation (consequence conseq)

-- | Check the validity of a consequence given an NMatrix, checking all possible valuations
isConsequenceValid :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Consequence -> m Bool
isConsequenceValid nmatrix conseq = null <$> isConsequenceValid' nmatrix conseq

-- | Check the validity of a consequence given an NMatrix, checking all possible valuations
isConsequenceValid' :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Consequence -> m [(Valuation a, [Formula])]
isConsequenceValid' nmatrix conseq = 
    case sigmaVarsFromConsequence conseq of
        Left e -> throwM e
        Right (_, vars) -> checkValuations valuations
            where
                values = (S.toList . fst . NMatrix.values) nmatrix
                valuations = generateValuations (S.toList vars) values

                checkValuations [] = return []
                checkValuations (v:vs) = 
                    case isConsequenceSatisfied' nmatrix v conseq of
                        Left e -> throwM e
                        Right [] -> checkValuations vs
                        Right fs -> do 
                                        zs <- checkValuations vs
                                        return $ (v,fs) : zs

-- | Check validity of a consequence relation given an NMatrix and a valuation 
isConseqRelationSatisfied :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Valuation a -> ConsequenceRelation -> m Bool
isConseqRelationSatisfied nmatrix valuation conseqrel = 
    null <$> isConseqRelationSatisfied' nmatrix valuation conseqrel

-- | Check validity of a consequence relation given an NMatrix and a valuation 
isConseqRelationSatisfied' :: (MonadThrow m, Ord a, Show a) => NMatrix a -> Valuation a -> ConsequenceRelation -> m [(Consequence, [Formula])]
isConseqRelationSatisfied' nmatrix valuation conseqrel = checkConseqRelation (S.toList conseqrel)
        where
            checkConseqRelation [] = return []
            checkConseqRelation (c:cs) = 
                case isConsequenceSatisfied' nmatrix valuation c of
                    Left e -> throwM e
                    Right [] -> checkConseqRelation cs
                    Right fs -> do 
                                    zs <- checkConseqRelation cs
                                    return $ (c, fs) : zs

-- | Check the validity of a consequence relation given an NMatrix, checking all possible valuations
isConseqRelationValid :: (MonadThrow m, Ord a, Show a) => NMatrix a -> ConsequenceRelation -> m Bool
isConseqRelationValid nmatrix conseqrel = null <$> isConseqRelationValid' nmatrix conseqrel

-- | Check the validity of a consequence relation given an NMatrix, checking all possible valuations
isConseqRelationValid' :: (MonadThrow m, Ord a, Show a) => NMatrix a -> ConsequenceRelation -> m [(Valuation a, [(Consequence, [Formula])])]
isConseqRelationValid' nmatrix conseqrel = 
    case varsFromConseqRelation conseqrel of
        Left e -> throwM e
        Right vars -> checkConseqRelationValidity valuations
            where
                values = (S.toList . fst . NMatrix.values) nmatrix
                valuations = generateValuations (S.toList vars) values
                checkConseqRelationValidity [] = return []
                checkConseqRelationValidity (v:vs) = 
                    case isConseqRelationSatisfied' nmatrix v conseqrel of
                        Left e -> throwM e
                        Right [] -> checkConseqRelationValidity vs
                        Right fs -> do
                                        zs <- checkConseqRelationValidity vs
                                        return $ (v, fs) : zs

-- | Check if a formula is a theorem. Demands completeness.
isFormulaTautology :: (MonadThrow m, Ord a, Show a) => Logic -> NMatrix a -> Formula -> m Bool
isFormulaTautology logic nmatrix formula =
    do
        isConseqValid <- isConseqRelationValid nmatrix conseqs
        if isConseqValid then 
            isFormulaValid nmatrix formula
        else return True
    where
        conseqs = conseqrel logic

-- | Generate valuations given a list of variables and values
generateValuations :: (Ord a) => [Variable] -> [a] -> [Valuation a]
generateValuations vars values = foldr f [] (replicateM n values)
    where   n = length vars
            f x xs = M.fromList (zip vars x) : xs

-- | Generate all NMatrices for a given set of values
generateNMatrices :: forall a m. (Traversable m, MonadThrow m, Ord a, Show a) => Signature -> Values a -> m [NMatrix a]
generateNMatrices sigma values = nmatrices
    where
        nmatrices = mapM (pure (NMatrix values) <*>) interpretations
        interpretations = mapM (pure M.fromList <*>) rawinterp
        rawinterp = sequence <$> truthTables
        truthTables = mapM f connects 
        connects = S.toList $ foldr S.union S.empty (M.elems sigma) 
        f :: Connective -> m [(Connective, TruthTable a)]
        f conn = mapM' ((,) conn) $ generateTruthTables (k conn) (fst values) 
        mapM' :: (TruthTable a -> (Connective, TruthTable a)) -> m [TruthTable a] -> m [(Connective, TruthTable a)]
        mapM' f l = 
            do
                l' <- l
                let l'' = map f l'
                return l''

-- | Check independence
-- Takes two sets A and B, B subset A, and informs the independence
checkIndependence :: forall a m. (Traversable m, MonadThrow m, Ord a, Show a) => Values a -> ConsequenceRelation -> ConsequenceRelation -> m Bool
checkIndependence values super sub = not . null <$> checkIndependence' values super sub

-- | Check independence
-- Takes two sets A and B, B subset A, and informs the independence
checkIndependence' :: forall a m. (Traversable m, MonadThrow m, Ord a, Show a) => Values a -> ConsequenceRelation -> ConsequenceRelation -> m [(NMatrix a, [(Valuation a, [(Consequence, [Formula])])])]
checkIndependence' values super sub =
    case sigmaFromConseqRelation super of
        Left e -> throwM e
        Right sig ->
            case generateNMatrices sig values of 
                Left e -> throwM e
                Right nms -> checkIndep nms
                where
                    diff = S.difference super sub
                    checkIndep [] = return []
                    checkIndep (m:ms) = 
                        case isConseqRelationValid' m diff of
                            Left e -> throwM e
                            Right [] -> case isConseqRelationValid' m sub of
                                            Left e -> throwM e
                                            Right [] -> checkIndep ms
                                            Right fs -> do
                                                            zs <- checkIndep ms
                                                            return $ (m, fs) : zs 
                            Right fs -> checkIndep ms

-- | Check rules validity for formulas and truth tables
consequenceValidityByNMatrix :: forall a m. (Traversable m, MonadThrow m, Ord a, Show a) => ConsequenceRelation -> Values a -> m [(NMatrix a, (ConsequenceRelation, ConsequenceRelation))]
consequenceValidityByNMatrix conseqrel values = 
    case sigmaFromConseqRelation conseqrel of
        Left e -> throwM e
        Right sigma -> case generateNMatrices sigma values of
                            Left e -> throwM e
                            Right nms -> mapM f nms
                                where 
                                    f nm = do
                                            (lt, lf) <- mpartition (isConsequenceValid nm) (S.toList conseqrel)
                                            return (nm, (S.fromList lt, S.fromList lf))
                                    mpartition :: forall a m. (Traversable m, MonadThrow m, Ord a, Show a) => (a -> m Bool) -> [a] -> m ([a],[a])
                                    mpartition _ [] = return ([],[])
                                    mpartition f (x:xs) = 
                                        do
                                            test <- f x
                                            (zs,ys) <- mpartition f xs
                                            if test then
                                                return (x:zs, ys)
                                            else 
                                                return (zs, x:ys)

-- | Build a truth table for a given derived connective
truthTableFromDerived :: forall a m. (MonadThrow m, Ord a, Show a, Eq a) => Formula -> NMatrix a -> m (TruthTable a)
truthTableFromDerived fmla nmatrix = 
        pure M.fromList <*> (pure zip <*> pure arguments <*> evaluations)
    where
        evaluations = mapM (flip (evaluate interpret) fmla) valuations
        valuations = M.fromList . zip variables <$> arguments
        variables = S.toList $ stringVarsFromFormula fmla
        arguments = generateTruthTableArgs (getFormulaArity fmla) ((fst . values) nmatrix)
        interpret = interpretation nmatrix
