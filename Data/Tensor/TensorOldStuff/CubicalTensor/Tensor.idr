module Tensor.CubicalTensor.Tensor

import Data.Fin
import Data.Vect

import Data.Functor.Naperian
import Misc

%hide Data.Vect.transpose


{-
Three main datatypes in this file:
data Tensor -> defines tensors
Array -> for ease of creation of tensors from lists
IndexTensor -> for easy indexing of tensors
-}

||| Defines the Tensor datatype
||| 
||| `n` is also often called rank of a tensor
public export
data Tensor : (shape : Vect n Nat) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : Vect d (Tensor ds dtype) -> Tensor (d :: ds) dtype

%name Tensor t, u, v

namespace TensorInterfaces
  public export
  Show a => Show (Tensor shape a) where
    show (TZ x) = show x
    show (TS xs) = show xs

  public export
  Eq a => Eq (Tensor shape a) where
    (TZ v1) == (TZ v2) = v1 == v2
    (TS xs) == (TS ys) = xs == ys

  public export
  Functor (Tensor shape) where
    map f (TZ x) = TZ (f x)
    map f (TS xs) = TS (map (map f) xs)

  public export
  Foldable (Tensor shape) where
    foldr f z (TZ x) = f x z 
    foldr f z (TS xs) = foldr (\t, acc => foldr f acc t) z xs 

  public export
  Traversable (Tensor shape) where
    traverse fn (TZ val) = TZ <$> fn val
    traverse fn (TS xs) = TS <$> traverse (traverse fn) xs



namespace NestedTensorStuff
  -- The maps below doesn't hold as equalities because:
  -- Tensor (n :: ns) a is a tensor of shape (n :: ns) with elements of type a
  -- Tensor [n] (Tensor ns a) would be a tensor of shape [n] with elements of type (Tensor ns a)
  -- 
  -- We can define functions that convert between these representations:

  public export
  toNestedTensor : Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
  toNestedTensor (TS vs) = TS (TZ <$> vs)

  public export
  fromNestedTensor : Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
  fromNestedTensor (TS vs) = TS ((\(TZ jk) => jk) <$> vs)


  -- More general version than above
  public export
  toNestedTensor : {sh1 : Vect n Nat} -> {sh2 : Vect m Nat}
    -> Tensor (sh1 ++ sh2) a -> Tensor sh1 (Tensor sh2 a)
  toNestedTensor {sh1 = []} {sh2} t = TZ t
  toNestedTensor {sh1 = (_ :: _)} {sh2} (TS xs) = TS $ toNestedTensor <$> xs

  public export
  fromNestedTensor : Tensor sh1 (Tensor sh2 a) -> Tensor (sh1 ++ sh2) a
  fromNestedTensor (TZ tv) = tv
  fromNestedTensor (TS xts) = TS $ map fromNestedTensor xts



public export
Scalar : (dtype : Type) -> Type
Scalar dtype = Tensor [] dtype

public export
Vector : (size : Nat) -> (dtype : Type) -> Type
Vector size dtype = Tensor [size] dtype

public export
Matrix : (rows, cols : Nat) -> (dtype : Type) -> Type
Matrix rows cols dtype = Tensor [rows, cols] dtype

namespace ApplicativeTensorA
  -- unit of a monoidal functor
  public export
  tensorReplicate : {shape : Vect n Nat} -> a -> Tensor shape a
  tensorReplicate {shape = []} a = TZ a
  tensorReplicate {shape = (n :: _)} a = TS (replicate n (tensorReplicate a))
  
  -- generalised zip
  -- laxator of a monoidal functor
  public export
  liftA2Tensor : Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
  liftA2Tensor (TZ a) (TZ b) = TZ (a, b)
  liftA2Tensor (TS as) (TS bs) = TS (zipWith liftA2Tensor as bs) 
  
  
  public export
  {shape : Vect n Nat} -> Applicative (Tensor shape) where
    pure x = tensorReplicate x
    fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs 

namespace NumericTensorA
  -- Pointwise Num structure
  public export
  {shape : Vect n Nat} -> Num a => Num (Tensor shape a) where
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys
    fromInteger = pure . fromInteger

  public export
  {shape : Vect n Nat} -> Neg a => Neg (Tensor shape a) where
    negate t = negate <$> t
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : Vect n Nat} -> Abs a => Abs (Tensor shape a) where
    abs t = abs <$> t



namespace ArrayT
  -- The point of this construction is to be able to easily create tensors using lists, without needing to use the inductive form requiring `TZ` and `TS`. 
  public export
  Array : (shape : Vect rank Nat) -> (dtype : Type) -> Type
  Array []        a = a
  Array (m :: ms) a = Vect m (Array ms a)

  public export
  fromArray : {shape : Vect rank Nat} -> Array shape a -> Tensor shape a
  fromArray {shape = []} y = TZ y
  fromArray {shape = (_ :: _)} y = TS (fromArray <$> y)

  public export
  toArray : {shape : Vect rank Nat} -> Tensor shape a -> Array shape a
  toArray (TZ x) = x
  toArray (TS xs) = toArray <$> xs

namespace IndexT
  ||| Machinery for indexing tensors
  ||| Given a tensor `Tensor [3, 4] Double` this allows us to index one of its elements, and provide a compile-time guarantee that we won't be out of bounds
  ||| See TensorExamples for examples of this in action
  public export
  data IndexT : (shape : Vect n Nat) -> Type where
    Nil  : IndexT []
    (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

  public export
  Show (IndexT shape) where
    show Nil = ""
    show (i :: is) = show i ++ ", " ++ show is

  -- Couterpart of 'index' for Vectors
  public export
  indexTensor : (index : IndexT shape)
              -> Tensor shape a
              -> a
  indexTensor [] (TZ val) = val
  indexTensor (indHere :: restOfIndex) (TS xs)
    = indexTensor restOfIndex (index indHere xs)


  -- Why can't I use @ here?
  public export infixr 9 @@

  public export
  (@@) : Tensor shape a -> IndexT shape -> a
  (@@) = flip indexTensor


  -- AI generated, not checked if correct
  tensorTabulate : {shape : Vect n Nat}
    -> (IndexT shape -> a) -> Tensor shape a
  tensorTabulate {shape = []} f = TZ (f Nil)
  tensorTabulate {shape = (s :: ss)} f = TS $ vectTabulate (\i => tensorTabulate {shape=ss} (\is => f (i :: is)))
  
  public export
  {shape : Vect n Nat} -> Naperian (Tensor shape) where
      Log = IndexT shape
      lookup = flip indexTensor
      tabulate = tensorTabulate

  -- using Naperian instance
  public export
  transposeMatrix : {i, j : Nat} -> Tensor [i, j] a -> Tensor [j, i] a
  transposeMatrix = fromNestedTensor . transpose . toNestedTensor



namespace SliceT
  ||| Machinery for slicing tensors
  ||| Crucially, different from the indexing one in the definition of (::)
  ||| Here we have Fin (S m) instead of Fin m
  public export
  data SliceT : (shape : Vect n Nat) -> Type where
    Nil : SliceT []
    (::) : Fin (S m) -> SliceT ms -> SliceT (m :: ms)

  public export
  sliceToShape : {shape : Vect n Nat} -> SliceT shape -> Vect n Nat
  sliceToShape Nil = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  public export --
  takeTensor : (slice : SliceT shape)
            -> Tensor shape a
            -> Tensor (sliceToShape slice) a
  takeTensor Nil (TZ val) = TZ val
  takeTensor (s :: ss) (TS xs) = TS $ (takeTensor ss) <$> takeFin s xs


namespace ReshapeT
  ||| Machinery for reshaping tensors
  ||| Still WIP
  public export
  reshapeTensor : Tensor shape a
              -> (newShape : Vect n Nat)
              -> {auto prf : prod shape = prod newShape}
              -> Tensor newshape a
  reshapeTensor t newShape = ?reshapeTensor_rhs



