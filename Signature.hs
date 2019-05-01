{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Signature (mkConnective, Signature, union, unionSignatures, k, symbol, Arity, mkSignatureFromConnectives, sigmaVarsFromFormula) where

import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Data.Aeson.Types
import GHC.Generics
import Connective
import Formula


-- | k-place connective
--data Connective = Connective {
--                    symbol :: String,
--                    k :: Arity
--                    } deriving (Show, Typeable, Eq, Ord, Generic, ToJSON, FromJSON, ToJSONKey)

-- | Signature, a family of k-place connectives
type Signature = Map Int (S.Set Connective)

-- | Errors about connectives
data ConnectiveException = NegativeArity | ImproperSymbol
        deriving (Show, Eq, Typeable)
instance Exception ConnectiveException

-- | Errors about signatures
data SignatureException = EmptySignature | DupConnectiveSymbol
        deriving (Show, Eq, Typeable)
instance Exception SignatureException

-- | Make a connective
mkConnective :: (MonadThrow m) => (String, Int) -> m Connective
mkConnective (s, i)
    | i < 0 = throwM NegativeArity
    | s == "" = throwM ImproperSymbol
    | otherwise = return $ Connective {symbol = s, k = i}

-- | Make signature from list of connectives
mkSignature :: (MonadThrow m) => [(String, Int)] -> m Signature
mkSignature cs
      | null cs = throwM EmptySignature
      | otherwise = mkSignature' empty cs
    where
        mkSignature' :: (MonadThrow m) => Signature -> [(String, Int)] -> m Signature
        mkSignature' sig [] = return sig
        mkSignature' sig (cp:cs) = case (mkConnective cp :: Either SomeException Connective) of
                                        Left e -> throwM e
                                        Right c' -> mkSignature' sig' cs
                                            where
                                            sig' = case sig !? arity of
                                                Nothing -> insert arity (S.fromList [c']) sig
                                                Just cs' -> insert arity (S.insert c' cs') sig
                                                where arity = k c'

-- | Make signature from list of connectives
mkSignatureFromConnectives :: (MonadThrow m) => [Connective] -> m Signature
mkSignatureFromConnectives cs
      | null cs = throwM EmptySignature
      | otherwise = mkSignature' empty cs
    where
        mkSignature' :: (MonadThrow m) => Signature -> [Connective] -> m Signature
        mkSignature' sig [] = return sig
        mkSignature' sig (cp:cs) = mkSignature' sig' cs
                                    where
                                    sig' = case sig !? arity of
                                        Nothing -> insert arity (S.fromList [cp]) sig
                                        Just cs' -> insert arity (S.insert cp cs') sig
                                        where arity = k cp
-- | Union of two signatures
union :: Signature -> Signature -> Signature
union = M.unionWith S.union

-- | Union signatures
unionSignatures :: [Signature] -> Signature
unionSignatures = foldr union M.empty

translation :: (MonadThrow m) => ([Formula] -> Connective -> Formula) -> Formula -> m Formula
translation _ f@(Var s) = pure f
translation t (Op s' fs) = flip t <$> mkConnective (s',(length fs)) <*> mapM (translation t) fs

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


