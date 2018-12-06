{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Signature (mkConnective, Signature, Connective, union, unionSignatures, k, symbol, Arity, mkSignatureFromConnectives) where

import Data.Map.Strict (Map, empty, insert, (!?), (!))
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Exception.Safe (Exception, MonadThrow, throwM, SomeException)
import Data.Typeable
import Data.Aeson.Types
import GHC.Generics

type Arity = Int

-- | k-place connective
data Connective = Connective {
                    symbol :: String,
                    k :: Arity
                    } deriving (Show, Typeable, Eq, Ord, Generic, ToJSON, FromJSON, ToJSONKey)

-- | Signature, a family of k-place connectives
type Signature = Map Int (S.Set Connective)

-- | Variable
type Variable = String

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
