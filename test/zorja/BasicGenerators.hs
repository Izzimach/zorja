module Zorja.BasicGenerators where

import qualified Data.Text as T

import Hedgehog
import Hedgehog.Gen
import Hedgehog.Range

basic_integergen :: (MonadGen m) => m Integer
basic_integergen = integral $ linearFrom (0::Integer) (-10000::Integer) (10000::Integer)

basic_floatgen :: Gen Float
basic_floatgen = float $ linearFracFrom (0.0::Float) (-10000.0::Float) (10000.0::Float)

basic_textgen :: Gen T.Text
basic_textgen = text (linear 0 20) unicode

basic_listgen :: (MonadGen m) => m a -> m [a]
basic_listgen a = list (linear 0 30) a
