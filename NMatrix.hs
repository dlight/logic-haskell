{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NMatrix (NMatrix(..), Values, generateTruthTables, generateTruthTableArgs, valuesFromLists, Interpretation, mkTruthTable, TruthTable, mkInterpretation, V, generateProjections, truthTableArity, superpose, mkInterpretation') where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Signature
import Formula (Symbol, Formula, getFormulaArity, varsFromFormula, stringVarsFromFormula)
import Control.Monad
import Data.Aeson.Types
import GHC.Generics (Generic)
import Connective

-- | V := Set of truth-values
type V a = S.Set a

-- | D \subset V := Set of designated values
type D a = S.Set a

-- | NMatrix values
type Values a = (V a, D a)  

-- | A truth table
type TruthTable a = M.Map [a] a

-- | Interpretations for each connective
type Interpretation a = M.Map Connective (TruthTable a)

-- | NMatrix by definition
data NMatrix a = NMatrix {values :: Values a, interpretation :: Interpretation a}
    deriving (Show, Generic, FromJSONKey, ToJSONKey, ToJSON, FromJSON, Eq)

-- | Exceptions regarding interpretations
data InterpretationException = 
    UnknownSymbol String    |
    MultipleDefinition String |
    MissingInterpretations Signature |
    ExcessInterpretations |
    InvalidSuperpositionArgsNumber Int |
    IncompatibleSuperpositionArities
    deriving (Show, Eq)

instance Exception InterpretationException

-- | Make a truth table from list
mkTruthTable :: (MonadThrow m, Show a, Ord a) => [([a],a)] -> m (TruthTable a)
mkTruthTable = foldr f (return M.empty)
    where 
        f (ps, r) table = 
            do
                table' <- table
                let curDim = length $ head $ M.keys table' in
                    if M.null table' || (length ps == curDim) then
                        M.insert ps r <$> table
                    else 
                        throwM MixedTableDimensions

-- | Produce a connective from a truth table
connectiveFromTruthTable :: (MonadThrow m, Show a, Ord a) => (Symbol, TruthTable a) -> m Connective
connectiveFromTruthTable (s, tt) 
    | M.null tt = mkConnective (s, 0)
    | otherwise = mkConnective (s, arity)
        where arity = length $ head $ M.keys tt

-- | Make an interpretation from a list of truth tables
mkInterpretation :: (MonadThrow m, Show a, Ord a) => Signature -> [(Symbol, TruthTable a)] -> m (Interpretation a)
mkInterpretation sig [] 
    | M.null sig = return M.empty
    | otherwise = throwM $ MissingInterpretations sig
mkInterpretation sig (c@(_,tt):cs) 
    | M.null sig = throwM ExcessInterpretations
    | otherwise = 
        case connectiveFromTruthTable c :: Either SomeException Connective of
            Left e -> throwM e
            Right connective ->  
                case sig M.!? k connective of
                    Nothing -> throwM $ UnknownSymbol $ symbol connective
                    Just set -> if S.member connective set then 
                                    let sig' = if S.size set == 1 then 
                                                    M.delete (k connective) sig
                                               else 
                                                    M.update (Just . S.delete connective) (k connective) sig in
                                        do 
                                            interp <- mkInterpretation sig' cs
                                            return $ M.insert connective tt interp
                                else 
                                    throwM $ UnknownSymbol $ symbol connective

-- | Make an interpretation from a list of truth tables
mkInterpretation' :: (MonadThrow m, Show a, Ord a) => [(Symbol, TruthTable a)] -> m (Interpretation a)
mkInterpretation' []            = return M.empty
mkInterpretation' (c@(_,tt):cs) = do
    connective <- connectiveFromTruthTable c
    M.insert connective tt <$> mkInterpretation' cs

truthTableArity :: (Show a, Ord a) => TruthTable a -> Int
truthTableArity tt = length firstArgEntry
    where (firstArgEntry, _) = head $ M.toList tt

-- | Superposition or multiple finitary composition
-- Given f, arity m, and g1,g2,...,gm, all arity n, call 
-- h(x1,x2,...,xn) = f(g1(x1,x2,...,xn),...,gm(x1,x2,...,xn)) a superposition.
superpose :: forall a m. (MonadThrow m, Show a, Ord a) => TruthTable a -> [TruthTable a] -> m (TruthTable a)
superpose f gs 
    | outerArity == 0 = return f -- when f is 0-ary
    | outerArity /= length gs = throwM $ InvalidSuperpositionArgsNumber outerArity -- when f expects more or less
    | not (null gs) && any (/= head gsArities) gsArities = throwM IncompatibleSuperpositionArities -- when gs are of different arity
    | otherwise = return $ foldr foldFunction M.empty args
        where   outerArity = truthTableArity f
                gsArities = map truthTableArity gs
                apply x = map (M.! x)
                foldFunction x = M.insert x ((M.!) f (apply x gs))
                args = S.toList $ M.keysSet $ head gs

-- | Exceptions regarding NMatrices
data NMatrixException = InvalidDesignated | 
                        MixedTableDimensions
                        deriving (Show, Eq, Typeable)

instance Exception NMatrixException

-- | Build the NMatrix values from lists
valuesFromLists :: (MonadThrow m, Ord a, Show a, Eq a) => [a] -> [a] -> m (V a, D a)
valuesFromLists vs ds 
    | ds' `S.isSubsetOf` vs' = return (ds', vs')
    | otherwise = throwM InvalidDesignated
        where 
            vs' = S.fromList vs
            ds' = S.fromList ds

-- | Generate truth tables given an arity and a values set
generateTruthTables :: (Ord a, Show a, MonadThrow m) => Arity -> V a -> m [TruthTable a]
generateTruthTables arity values = mapM mkTruthTable argsTruthTables
    where
        argsTruthTables = Prelude.map (zip args) images
        args = replicateM arity (S.toList values)
        images = replicateM k (S.toList values)
        k = S.size values ^ arity

-- | Generate arguments for a truth table
generateTruthTableArgs :: forall a m. (Ord a, Show a) => Arity -> V a -> [[a]]
generateTruthTableArgs k vs = replicateM k (S.toList vs)

-- | Generate projections of a given arity
generateProjections :: forall a m. (MonadThrow m, Ord a, Show a) => Arity -> V a -> m [TruthTable a]
generateProjections arity vs = mapM ithProjection [0..(arity-1)]
    where
        ithProjection :: (MonadThrow m, Ord a, Show a) => Arity -> m (TruthTable a)
        ithProjection i = mkTruthTable $ zip args (images i)
        images i = Prelude.map (flip (!!) i) args
        args = replicateM arity (S.toList vs)
