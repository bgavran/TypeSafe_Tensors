module Architectures.Linear

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tensor.Tensor
import Data.Tensor.Utils
import Para.Para
import Architectures.Softmax
import Algebra
import Misc


public export
linearImpl : {x, y : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext x) => Applicative (Ext y) => 
  AllAlgebra [x] a =>
  TensorA [y, x] a -> TensorA [y] a -> TensorA [x] a -> TensorA [y] a
linearImpl weights bias input = matrixVectorProductA weights input + bias

linearImpl' : {i, j : Nat} -> {a : Type} -> Num a =>
  Tensor [j, i] a -> Tensor [j] a -> Tensor [i] a -> Tensor [j] a
linearImpl' = ?ghh -- linearImpl {x=Vect i, y=Vect j} {a}

linearImplTreeLeaf : {a : Type} -> Num a =>
  TensorA [BTreeLeaf, BTreeLeaf] a ->
  TensorA [BTreeLeaf] a ->
  TensorA [BTreeLeaf] a ->
  TensorA [BTreeLeaf] a
linearImplTreeLeaf = linearImpl

public export
linearPara : {x, y : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext x) => Applicative (Ext y) => 
  AllAlgebra [x] a =>
  Para (TensorA [x] a) (TensorA [y] a)
linearPara = MkPara
  (const (TensorA [y, x] a, TensorA [y] a))
  (\input, (weights, bias) => linearImpl weights bias input)


-- linearPara' : {i, j : Nat} -> {a : Type} -> Num a =>
--   Para (Tensor [i] a) (Tensor [j] a)
-- linearPara' = ?ghh -- linearPara {x=Vect i, y=Vect j} {a}
