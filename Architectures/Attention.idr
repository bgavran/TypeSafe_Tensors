module Architectures.Attention

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.TreeUtils

import Data.Tensor.Tensor
import Data.Tensor.Utils
import Data.Tree
import Para.Para
import Architectures.Softmax
import Algebra
import Misc

parameters {a : Type} {auto _ : Num a}

  ||| Generalised form of attention
  public export
  crossAttention : {inputStructure, crossStructure, features : Cont} ->
    Applicative (Ext inputStructure) =>
    Applicative (Ext crossStructure) =>
    Applicative (Ext features) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (q : TensorA [inputStructure, features] a) ->
    (k : TensorA [crossStructure, features] a) ->
    (v : TensorA [inputStructure, features] a) ->
    TensorA [crossStructure, features] a
  crossAttention {allAlg = ((::) {allAlg=_})} softmax q k v =
    let attentionMatrix : TensorA [crossStructure, inputStructure] a
        attentionMatrix = softmax <-$-> (q `matrixMatrixProductA` k)
    in attentionMatrix `matMulA` v
  

  ||| Self-attention is cross-attention where inputStructure = crossStructure
  public export
  selfAttention : {inputStructure, features : Cont} ->
    Applicative (Ext inputStructure) =>
    Applicative (Ext features) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (q : TensorA [inputStructure, features] a) ->
    (k : TensorA [inputStructure, features] a) ->
    (v : TensorA [inputStructure, features] a) ->
    TensorA [inputStructure, features] a
  selfAttention = crossAttention

  ||| Self-attention for cubical tensors
  public export
  selfAttention' : {inputSize, featureSize : Nat} ->
    (softmax' : Tensor [inputSize] a -> Tensor [inputSize] a) ->
    (q : Tensor [inputSize, featureSize] a) ->
    (k : Tensor [inputSize, featureSize] a) ->
    (v : Tensor [inputSize, featureSize] a) ->
    Tensor [inputSize, featureSize] a
  selfAttention' softmax' (ToCubicalTensor q) (ToCubicalTensor k) (ToCubicalTensor v)
    = ToCubicalTensor $ selfAttention (FromCubicalTensor . softmax' . ToCubicalTensor) q k v


  ||| Data structure for holding parameters of self-attention
  record SelfAttentionParams
    (features : Cont)
    {auto prf : Applicative (Ext features)}
    where
    constructor MkSAParams
    queryMatParam : TensorA [features, features] a
    keyMatParam : TensorA [features, features] a
    valueMatParam : TensorA [features, features] a

  ||| Forward pass of self-attention
  SAImpl : {inputStructure, features : Cont} ->
    Applicative (Ext inputStructure) => Applicative (Ext features) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (input : TensorA [inputStructure, features] a) ->
    (params : SelfAttentionParams features) ->
    TensorA [inputStructure, features] a
  SAImpl {allAlg = ((::) {allAlg=_})} softmax input (MkSAParams queryMat keyMat valueMat)
    = let queries = queryMat `matrixMatrixProductA` input
          keys = keyMat `matrixMatrixProductA` input
          values = valueMat `matrixMatrixProductA` input
    in selfAttention softmax queries keys values

  ||| Self-attention as a parametric map
  public export
  SelfAttention : {inputStructure, features : Cont} ->
    Applicative (Ext inputStructure) => Applicative (Ext features) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a)
    -> Para (TensorA [inputStructure, features] a)
            (TensorA [inputStructure, features] a)
  SelfAttention softmax = MkPara
    (const (SelfAttentionParams features))
    (SAImpl softmax)


  ||| Self-attention for cubical tensors as a parametric map
  public export
  SelfAttention' : {inputSize, featureSize : Nat} ->
    (softmax' : Tensor [inputSize] a -> Tensor [inputSize] a) ->
    Para (Tensor [inputSize, featureSize] a)
         (Tensor [inputSize, featureSize] a)
  SelfAttention' softmax' = MkPara
    (const (SelfAttentionParams (Vect featureSize)))
    (\inp => ToCubicalTensor . (SAImpl {features=Vect featureSize} (FromCubicalTensor . softmax' . ToCubicalTensor) (FromCubicalTensor inp)))
  

-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Tensor [n, d] Double) (Tensor [n, d] Double)
SelfAttentionMat = SelfAttention' softmax'

-- Self Attention for trees
SelfAttentionTree : {d : Nat} -> Para
  (TensorA [BTreeLeaf, Vect d] Double)
  (TensorA [BTreeLeaf, Vect d] Double)
SelfAttentionTree = SelfAttention softmaxBTreeLeaf


--------------------
-- Examples
--------------------
-- Will run self attention as usual, on matrices, and one on trees


||| Consume an input matrix, parameters, and produce the output of a self-attention layer
SAMatrixForwardPass : {n, d : Nat}
  -> (input : Tensor [n, d] Double)
  -> (p : Param SelfAttentionMat input)
  -> Tensor [n, d] Double
SAMatrixForwardPass = Run SelfAttentionMat


inputMatrix : Tensor [4, 2] Double
inputMatrix = fromArray [ [1, 3]
                         , [2, 8]
                         , [0, 0]
                         , [1, 3]]

||| Parameters for self-attention
||| Here just a matrix of ones
params : {d : Nat} -> SelfAttentionParams (Vect d) {a=Double}
params = MkSAParams onesA onesA onesA

||| Example output for cubical self-attention
SAOutputMatrix : Tensor [4, 2] Double
SAOutputMatrix = SAMatrixForwardPass inputMatrix params

||| Consume a tree of vectors of features, parameters, and produce the output of a self-attention layer
SATreeForwardPass : {d : Nat}
  -> (input : TensorA [BTreeLeaf, Vect d] Double)
  -> (p : Param SelfAttentionTree input)
  -> TensorA [BTreeLeaf, Vect d] Double
SATreeForwardPass = Run SelfAttentionTree


tree1 : TensorA [BTreeLeaf, Vect 2] Double
tree1 = fromArrayA $ fromBTreeLeaf $ 
  Node' (Leaf (fromVect [4, 5])) (Leaf (fromVect [-12, 25]))

||| Example output for tree self-attention
SAOutputTree : TensorA [BTreeLeaf, Vect 2] Double
SAOutputTree = SATreeForwardPass tree1 params