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
                    } | DerivedConnective Formula 
                    deriving (Show, Typeable, Eq, Ord, Generic, ToJSON, FromJSON, ToJSONKey)
