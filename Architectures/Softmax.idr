module Architectures.Softmax

import Data.Vect
import Data.Vect.Elem

import Data.Container.Definition
import Data.Container.Instances
import Tensor.ContainerTensor.Tensor
-- import ApplicativeLinAlg
import Algebra
import Data.Tree
import Misc

public export
softmax : {i : Cont} -> {a : Type} -> Fractional a => Exp a =>
  {default 1 temperature : a} ->
  Applicative (Ext i) => (allAlg : AllAlgebra [i] a) =>
  Tensor [i] a -> Tensor [i] a
softmax {temperature} t = let exps = exp <$> (t <&> (/ temperature))
                          in exps <&> (/ (reduce exps))



||| Softmax for a cubical 1D tensor, i.e. a vector
public export
softmax' : {i : Nat} -> {a : Type} -> Fractional a => Exp a => 
  {default 1 temperature : a} ->
  Tensor' [i] a -> Tensor' [i] a
softmax' {temperature} t = let exps = exp <$> (t <&> (/ temperature))
                           in exps <&> (/ (reduce exps))


public export
softmaxBTreeLeaf : {a : Type} -> Fractional a => Exp a =>
  Tensor [BTreeLeafCont] a -> Tensor [BTreeLeafCont] a
softmaxBTreeLeaf = softmax

public export
softmaxBTreeNode : {a : Type} -> Fractional a => Exp a =>
  Tensor [BTreeNodeCont] a -> Tensor [BTreeNodeCont] a
softmaxBTreeNode = softmax


-- public export
-- softmax : {f : Type -> Type}
--   -> (Functor f, Algebra f a, Fractional a, Exp a) => f a -> f a
-- softmax {f} xs = let exps = exp <$> xs
--                  in exps <&> (/ reduce exps)
-- 
-- softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
-- softmaxVect = softmax
-- 
-- softmaxTreeLeaf : BTreeLeaf Double -> BTreeLeaf Double
-- softmaxTreeLeaf = softmax {f=BTreeLeaf}
-- 
-- softmaxTreeNode : BTreeNode Double -> BTreeNode Double
-- softmaxTreeNode = softmax {f=BTreeNode}

--- Tensor softmax

-- -- This should be done by a more general map operation over a specific axis
-- public export
-- softmax1 : {s : Cont} -> {ss : ApplV conts} ->
--   Applicative (Ext s) =>
--   Fractional (Tensor ss a) =>
--   Exp (Tensor ss a) => 
--   (allAlgebra : AllAlgebra [s] (Tensor ss a)) =>
--   Tensor (s :: ss) a -> Tensor (s :: ss) a
-- softmax1 {allAlgebra} x
--    = let sm = softmax' {i=s} {a=(Tensor ss a)}
--          t = tensorMapFirstAxis {x=s, y=s} sm 
--     in ?fmft
             


-- softmaxVect' : {n : Nat} -> Tensor [VectCont n] Double -> Tensor [VectCont n] Double
-- softmaxVect' = softmax'
-- 
-- softmaxBTreeLeaf' : Tensor [BTreeLeafCont] Double -> Tensor [BTreeLeafCont] Double
-- softmaxBTreeLeaf' = softmax'
-- 
-- softmaxBTreeNode' : Tensor [BTreeNodeCont] Double -> Tensor [BTreeNodeCont] Double
-- softmaxBTreeNode' = softmax'
 


-- TODO
-- namedSoftmax : {axis : Type -> Type}
--   -> {shape : Vect n ApplF} -> {a : Type}
--   -> Functor axis
--   => Elem axis shape
--   -> Tensor shape a
--   -> Tensor shape a
-- namedSoftmax {shape = []} axis t impossible -- can't be in vector if vector empty
-- namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
-- namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
