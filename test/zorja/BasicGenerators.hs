module Zorja.BasicGenerators where

import qualified Data.Text as T

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

basic_intgen :: (MonadGen m) => m Integer
basic_intgen = Gen.integral $ Range.linear (-10000::Integer) (10000::Integer)

basic_floatgen :: Gen Float
basic_floatgen = Gen.float $ Range.linearFrac (-10000.0::Float) (10000.0::Float)

basic_textgen :: Gen T.Text
basic_textgen = Gen.text (Range.linear 0 20) Gen.unicode

basic_listgen :: (MonadGen m) => m a -> m [a]
basic_listgen a = Gen.list (Range.linear 0 30) a
