{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Formula where

import Text.Read
import Signature
import qualified Data.Map.Strict as M
import qualified Data.Set as S
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
                            Ident i <- lexP
                            do
                                do
                                    Punc "(" <- lexP
                                    Punc ")" <- lexP
                                    return $ Op i []
                                +++
                                do
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

substitution :: Variable -> Formula -> Formula -> Formula
substitution v f f'@(Var s) = if v == s then f else f'
substituiion v f (Op s fs) = Op s (map (substitution v f) fs)

translation :: (MonadThrow m) => ([Formula] -> Connective -> Formula) -> Formula -> m Formula
translation _ f@(Var s) = pure f
translation t (Op s' fs) = flip t <$> mkConnective (s',(length fs)) <*> mapM (translation t) fs
