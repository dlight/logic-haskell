{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module Connective where

import Formula
import Data.Typeable
import Data.Aeson.Types
import GHC.Generics

type Arity = Int

data Connective = Connective {
                        symbol :: String,
                        k :: Arity
                    } 
--                    DerivedConnective {
--                        symbol :: String,
--                        fmla :: Formula 
--                    }
                    deriving (Show, Typeable, Eq, Ord, Generic, ToJSON, FromJSON, ToJSONKey, FromJSONKey)

-- | Induces a formula from a connective
formulaFromConnective :: Connective -> Formula
formulaFromConnective (Connective s k) = Op s variables
    where variables = map (Var . ("p"++) . show) [1..k]
-- formulaFromConnective (DerivedConnective _ fmla) = fmla


