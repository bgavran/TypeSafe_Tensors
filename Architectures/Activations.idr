module Architectures.Activations

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tensor.Tensor

import Misc


public export
relu : {a : Type} -> Ord a  => Num a => a -> a
relu x = max 0 x

public export
sigmoid : {a : Type} -> Neg a => Fractional a => Exp a => Num a =>
  a -> a
sigmoid x = 1 / (1 + ex) where ex = exp x

