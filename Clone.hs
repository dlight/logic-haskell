module Clone where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Either
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Control.Monad.State.Lazy
import Semantics
import NMatrix
import Formula
import Connective

-- | A universal algebraic Clone
newtype Clone a = Clone {
    functions :: S.Set (TruthTable a)
} deriving Show

type CloneGenerationState a = (Clone a)

-- | Given base sets of function over {0,1} A and B, 
-- informs if the connectives in B are in the clone
-- generated by A.
isInClone :: (MonadThrow m) => NMatrix Int -> NMatrix Int -> m Bool
isInClone baseA baseB = 
    do 
        aritiesB <- return $ interpretationArities (interpretation baseB) 
        projections <- mapM ((flip generateProjections) (fst (values baseA))) (S.toList aritiesB)
        let startState = Clone (S.fromList $ concat projections) in
            evalState (isInClone_ baseB baseA) startState

-- | Given a base set as initial state A and B another base set of functions over {0,1}, determine
-- if B is in the clone generated by A.
isInClone_ :: (MonadThrow m) => NMatrix Int -> NMatrix Int -> State (CloneGenerationState Int) (m Bool)
isInClone_ baseB baseA = 
    do
        fs <- get
        let aritiesB = S.toList $ interpretationArities (interpretation baseB) 
            opsBaseA = M.elems (interpretation baseA)
            opsBaseB = S.fromList $ M.elems (interpretation baseB)
            -- | truth tables per arity
            ttsByArity k = filter ((k==) . truthTableArity) (S.toList $ functions fs) 
            -- | all superpositions arity k with head tt
            allsuperpose tt k = mapM (superpose tt) (replicateM (truthTableArity tt) (ttsByArity k)) 
            -- | all superposition of arity k using heads in baseA
            superposeInBase k = mapM (flip allsuperpose k) opsBaseA in
            do
                case mapM superposeInBase aritiesB of
                    Left e -> undefined
                    Right deltaToConcat -> 
                        let delta = S.fromList (concat (concat deltaToConcat))
                            --diff = S.difference delta (functions fs) in
                            union = S.union delta (functions fs) in
                            if opsBaseB `S.isSubsetOf` union then
                                return $ return True
                            else if union `S.isSubsetOf` functions fs then
                                return $ return False 
                            else
                                return $ evalState (isInClone_ baseB baseA) (Clone union)

generateClone :: (MonadThrow m) => NMatrix Int -> [Int] -> m (Clone Int)
generateClone baseA arities = 
    do 
        projections <- mapM ((flip generateProjections) (fst (values baseA))) arities
        let startState = Clone (S.fromList $ concat projections) in
            evalState (generateClone_ baseA arities) startState

-- | Given a base set as initial state A and B another base set of functions over {0,1}, determine
-- if B is in the clone generated by A.
generateClone_ :: (MonadThrow m) => NMatrix Int -> [Int] -> State (CloneGenerationState Int) (m (Clone Int))
generateClone_ baseA arities = 
    do
        fs <- get
        let --aritiesB = S.toList $ interpretationArities (interpretation baseB) 
            opsBaseA = M.elems (interpretation baseA)
            --opsBaseB = S.fromList $ M.elems (interpretation baseB)
            -- | truth tables per arity
            ttsByArity k = filter ((k==) . truthTableArity) (S.toList $ functions fs) 
            -- | all superpositions arity k with head tt
            allsuperpose tt k = mapM (superpose tt) (replicateM (truthTableArity tt) (ttsByArity k)) 
            -- | all superposition of arity k using heads in baseA
            superposeInBase k = mapM (flip allsuperpose k) opsBaseA in
            do
                case mapM superposeInBase arities of
                    Left e -> undefined
                    Right deltaToConcat -> 
                        let delta = S.fromList (concat (concat deltaToConcat))
                            --diff = S.difference delta (functions fs) in
                            union = S.union delta (functions fs) in
                            if union `S.isSubsetOf` functions fs then
                                return $ return (Clone union)
                            else
                                return $ evalState (generateClone_ baseA arities) (Clone union)

interpretationArities :: (Show a, Ord a) => Interpretation a -> S.Set Int
interpretationArities int = S.fromList $ map truthTableArity (M.elems int)

-- | Given a base set as initial state A and B another base set of functions over {0,1}, determine
-- they are term equivalent
isTermEquivalent baseA baseB = pure (&&) <*> ltr <*> rtl
    where
        ltr = isInClone baseA baseB
        rtl = isInClone baseB baseA



