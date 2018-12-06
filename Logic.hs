{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Logic (Logic, Consequence, emptyLogic, ConsequenceRelation, sigmaFromConsequence, sigmaFromConseqRelation, consequence, predecessors, sigmaVarsFromConsequence, varsFromConseqRelation, conseqrel, sigma, makeLogic) where

import Signature
import Formula
import qualified Data.Set as S
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Data.Aeson.Types
import GHC.Generics (Generic)
import qualified Data.Map.Strict as M
import Text.Read

-- | Exceptions related to logic creation and maintenance
data LogicException = 
    FormulaOutsideLanguage
    deriving (Show, Eq, Typeable)

instance Exception LogicException

-- | A consequence in a consequence relation
data Consequence = Consequence { 
    predecessors :: S.Set Formula,
    consequence :: Formula
    } deriving (Show, Eq, Ord, Generic, ToJSON)

instance Read Consequence where
    readPrec = 
            prec up_prec $ do
                Punc "{" <- lexP
                do
                    do
                        Punc "}" <- lexP
                        Punc "|" <- lexP
                        f <- readPrec
                        return $ Consequence {predecessors = S.empty, consequence = f}
                    +++
                    do 
                        fs <- readListPrec
                        Punc "}" <- lexP
                        Punc "|" <- lexP
                        f <- readPrec
                        return $ Consequence {predecessors = S.fromList fs, consequence = f}
                where   app_prec = 10
                        up_prec = 5
            
    readListPrec = readListPrecDefault

-- | Consequence relation
type ConsequenceRelation = S.Set Consequence

-- | A logic
data Logic = Logic {
    sigma :: Signature, 
    conseqrel :: ConsequenceRelation
    } deriving (Show, Eq, Generic, ToJSON)

-- | Make a consequence from a pair
makeConsequence :: ([Formula], Formula) -> Consequence
makeConsequence (gamma, f) = Consequence {predecessors = S.fromList gamma, consequence = f}

-- | Make a consequence relation from pairs of raw consequences
makeConsequenceRelation :: [([Formula],  Formula)] -> ConsequenceRelation
makeConsequenceRelation = S.fromList . map makeConsequence

-- | Make a logic, given signatures and a consequence relation
-- Deals with incompatibilities between the signature and the
-- language in which the formulas are contained.
makeLogic :: (MonadThrow m) => Signature -> [Consequence] -> m Logic
makeLogic sigma = foldr f (return $ emptyLogic sigma)
    where f c ml = 
                    do
                        l <- ml
                        insertConseq l c

-- | Creates an empty logic (no consequence rules) from a signature
emptyLogic :: Signature -> Logic
emptyLogic sigma = Logic {sigma = sigma, conseqrel = S.empty}

-- | Insert a consequence into a logic
insertConseq :: (MonadThrow m) => Logic -> Consequence -> m Logic
insertConseq l c = do
            sigmaConseq <- sigmaFromConsequence c
            insertConseq' l c sigmaConseq
    where
        insertConseq' l c sigmaConseq
            | M.isSubmapOfBy (S.isSubsetOf) sigmaConseq (sigma l) = return $ Logic { sigma = sigma l, conseqrel = S.insert c (conseqrel l)}
            | otherwise = throwM FormulaOutsideLanguage

-- | Extract sigma and vars from consequence
sigmaVarsFromConsequence :: (MonadThrow m) => Consequence -> m (Signature, S.Set Variable)
sigmaVarsFromConsequence c = do
    let fs = formulas c
    ss <- sigmas fs
    return $ foldr f (M.empty, S.empty) ss
        where   
            f (x, y) (xs, ys) = (Signature.union x xs, S.union y ys)
            formulas c = consequence c : S.toList (predecessors c)
            sigmas [] = return []
            sigmas (f:fs) = do 
                    s <- sigmaVarsFromFormula f
                    ss <- sigmas fs
                    return (s:ss)

-- | Given a consequence, extract the induced signature
sigmaFromConsequence :: (MonadThrow m) => Consequence -> m Signature
sigmaFromConsequence c = pure fst <*> sigmaVarsFromConsequence c

-- | Given a consequence, extract the set of variables
varsFromConsequence :: (MonadThrow m) => Consequence -> m (S.Set Variable)
varsFromConsequence c = pure snd <*> sigmaVarsFromConsequence c
                
-- | Acts like sequence, but applies a function
sequenceMap :: (MonadThrow m) => ([a] -> b) -> [m a] -> m b
sequenceMap f lm = do
                l <- sequence lm
                return $ f l

-- | Extract signature and vars from a consequence relation
varsFromConseqRelation :: (MonadThrow m) => ConsequenceRelation -> m (S.Set Variable)
varsFromConseqRelation conseqrel = 
    foldr f (return S.empty) varSets
        where 
            f s ss = pure S.union <*> s <*> ss
            varSets = (map varsFromConsequence . S.toList) conseqrel

-- | Extract the signature from a consequence relation
sigmaFromConseqRelation :: (MonadThrow m) => ConsequenceRelation -> m Signature
sigmaFromConseqRelation = sequenceMap unionSignatures . map sigmaFromConsequence . S.toList 
