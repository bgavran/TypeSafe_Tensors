module Data.Tensor.CubicalTensorView

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.Fin.Arith

import Data.Tensor.Tensor
import Misc

||| This only works for cubical tensors
||| This is okay, because reshape only works for cube-shaped tensors
public export
record TensorView (shape : List Nat) (dtype : Type) where
    constructor MkTensorView
    flatData : Vect (prod shape) dtype

reshape : {oldShape : List Nat} -> {newShape : List Nat} ->
  {auto prf : prod newShape = prod oldShape} ->
  TensorView oldShape a ->
  TensorView newShape a
reshape {prf} (MkTensorView flatData) = MkTensorView (rewrite prf in flatData)


{-
Fix shape = [3, 4, 5]. This is 60 positions (prod shape). Three 4x5 matrices.
Let's study three examples of indexes into this shape.
- - - - -
- - - - -
- i - - -
- - - - k

- - - - -
- - - - -
- - - j -
- - - - -

- - - - -
- - - - -
- - - - -
- - - - -

Fix index k = [0, 3, 4]. This means indexing in the 1st matrix, 4th row, 5th column.
As flat data, the index of k=[0, 3, 4] can be computed as
k = 0 * (4 * 5)
  + 3 * (5)
  + 4 * 1
  = 19

Fix index i = [0, 2, 1]. This means indexing in the 1st matrix, 3rd row, 2nd column.
As flat data, this means
i = 0 * (4 * 5)
  + 2 * (5)
  + 1 * 1
  = 11

Fix index j = [1, 2, 3]. This means indexing in the 2nd matrix, 3st row, 4th column.
As flat data, this means indexing into the location given by 
j = 1 * (4 * 5 * 1)
  + 2 * (5 * 1)
  + 3 * 1
  = 33
-----------------------------------------------

Fix shape = [3, 4]. This is 12 positions.
- i - -
- - - -
- - - -

Fix index i = [0, 1]. This means indexing in the 1st row, 2nd column.
As flat data, this means
i = 0 * (4)
  + 1 * 1
  = 1


What all of these examples share in common?
Given shape : List Nat, the way we compute index is by taking a dot product of it with another vector computed *from* shape.
That other vector is called strides.

We now define the stride : Vect n Nat -> Vect n Nat function
-}

-- Here strides are in terms of number of elements, not bytes
public export
strides : (shape : Vect n Nat) -> Vect n Nat
strides [] = []
strides (s :: ss) = prod ss :: strides ss

example1 : strides [2,3,4,5] = [60, 20, 5, 1]
example1 = Refl

example2 : strides [3,4,5] = [20, 5, 1]
example2 = Refl

example3 : strides [4, 5] = [5, 1]
example3 = Refl

||| It will be important to prove later that if all elements of shape are non-zero, then the head of the strides is also non-zero
public export
stridesProofHeadNonZero : {shape : Vect (S n) Nat} ->
  {auto prf : All IsSucc shape} ->
  IsSucc (head (strides shape))
stridesProofHeadNonZero {shape = (_ :: ss)} {prf = (_ :: ps)}
  = allSuccThenProdSucc ss

||| Datatype defining the type of the index given a shape
||| This is 0-based indexing
public export
data IndexT : (shape : Vect n Nat) -> Type where
  Nil  : IndexT []
  (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

||| Given a shape and an index, compute the index in the flattened tensor
indexCount : {shape : Vect n Nat} -> {auto allNonZero : All IsSucc shape} ->
  IndexT shape -> Fin (prod shape)
indexCount {shape = []} _ = FZ
indexCount {shape = (s :: ss)} {allNonZero = (_ :: ps)} (i :: is)
  = let restCount = indexCount is
        restCountWeakened = weakenMultN s restCount
        
        strideHeadNonZero = stridesProofHeadNonZero {shape=(s :: ss)}
        hereCount = shiftMul (head (strides (s :: ss))) i
    in addFinsBounded hereCount restCountWeakened

indexCountExample1 : indexCount {shape = [3, 4, 5]} [0, 3, 4] = 19 -- : Fin 60
indexCountExample1 = Refl

indexCountExample2 : indexCount {shape = [3, 4, 5]} [0, 2, 1] = 11 -- : Fin 60
indexCountExample2 = Refl

indexCountExample3 : indexCount {shape = [3, 4, 5]} [1, 2, 3] = 33 -- : Fin 60
indexCountExample3 = Refl

indexCountExample4 : indexCount {shape = [3, 4]} [0, 1] = 1 -- : Fin 12
indexCountExample4 = Refl




{-
             0   1    2 
stride = 0   0   0    0
stride = 1   0   1    2
stride = 2   0   2    4
stride = 3   0   3    6
-}

-- ||| Note: (prod shape) can be zero. This means the argument (i : IndexT shape) can never be produced, as (prod shape) == 0 implies that one of the elements of shape is zero. This prevents us from being required to produce an uninhabited output type: Fin 0.
-- indexCount : (shape : List Nat) -> (i : IndexT shape) -> Fin (prod shape)
-- indexCount shape i
--   = let str = strides (fromList shape)
--     in ?indexCount_rhs


-- TODO this is technically quite inefficient since we recompute prod ss recursively
-- probably could use a helper function here?
-- bably could use a helper function here?
-- indexCount [] [] = 0
-- ind xCount (s :: ss) (i :: is) =
--     let ii : Fin s := i
--         pr : Nat := prod ss -- we want to turn this into Fin (prod ss)
--         tl : Fin (S (prod ss)) := natToFinLT (prod ss) {prf=reflexive}
--         -- prFin : Fin pr := natToFinLT (pred pr)
--         -- firstCompFin : Fin (finToNat i * pr)
--         --   := natToFinLT (finToNat i * pr) {n=finToNat i * pr}
--         restOfIndex : Fin (prod ss) := indexCount ss is  -- Fin 
--     in ?indexCount_rhs_2



{-
old:

indexCount [2, 3] : (index : IndexT [2, 3]) -> Fin 6
indexCount [2, 3] 


In other words, there should be a function
indexCount : (shape : Vect n Nat) -> (index : IndexT shape) -> Fin (prod shape)
indexCount shape index = index[0] * (prod shape[1..])
                       + index[1] * (prod shape[2..])
                       + ...
                       + index[n-1] * (prod shape[n..])
                       + index[n] * prod []

i.e.
indexCount [] [] = 0
indexCount (s :: ss) (i :: is) = i * (prod ss) + indexCount ss is
-----------------------------    ------------    ----------------
      Fin( prod(s :: ss))      Fin (s * prod ss) +  Fin (prod ss)

oooold
||| In simple terms, we want to do (i * str)
ddFin : {stride : Nat} ->
  {n : Nat} -> (i : Fin n) -> NonZero stride -> Fin (n * stride)
ddFin {n=0} FZ _ impossible
ddFin {n=0} (FS i) _ impossible
ddFin {n = (S n')} i (ItIsSucc {n=str})
  = let rl : (stride = (S str)) := %search
        strAsFin : Fin stride := natToFinLT str {prf=reflexive}
        pp : Fin (S (n' * str)) := i * strAsFin
    in ?ddFin_rhs_4
-- ddFin {n = (S n)} FZ (ItIsSucc {n=str}) = FZ
-- ddFin {n = (S n)} (FS i) (ItIsSucc {n=str})
--   = let rl : (stride = (S str)) := %search
--         strAsFin : Fin stride := natToFinLT str {prf=reflexive}
--         pp : Fin (S (n * str)) := (FS i) * strAsFin
--     in ?ddFin_rhs_4
-- 



-}