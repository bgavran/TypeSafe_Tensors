module Tensor.GeneralisedTensor.Tensor

import Data.Vect
import Data.Vect.Quantifiers

-- import Tensor
import Algebra
import Tree
import Data.Num
import Misc

%hide Builtin.infixr.(#)
-- %hide Tensor.tensorReplicate


public export prefix 0 #

||| Applicative functor with a proof
public export
record ApplF where
  constructor (#)
  F : Type -> Type
  {auto prf : Applicative F}

||| Generalised tensors
||| For storing not necessarily cube-like structures
public export
data Tensor : (shape : Vect n ApplF)
              -> (dtype : Type)
              -> Type where
  GTZ : (a : dtype) -> Tensor [] dtype
  GTS : Applicative f => f (Tensor ds dtype) -> Tensor ((# f) :: ds) dtype

%name Tensor t, u, v

namespace EqTensorA
  public export
  data AllEq : (shape : Vect n ApplF) -> (dtype : Type) -> Type where
    NilEq : Eq a => AllEq [] a
    ConsEq : Applicative f => Eq (f (Tensor fs dtype)) => AllEq ((# f) :: fs) dtype

  public export
  genTensorEq : (allEq : AllEq shape a) => Tensor shape a -> Tensor shape a -> Bool
  genTensorEq (GTZ x) (GTZ y) {allEq = NilEq} = x == y
  genTensorEq (GTS xs) (GTS ys) {allEq = ConsEq} = xs == ys

  public export
  (allEq : AllEq shape a) => Eq (Tensor shape a) where
    (==) = genTensorEq

namespace ShowTensorA
  public export
  data AllShow : (shape : Vect n ApplF) -> (dtype : Type) -> Type where
    NilShow : Show a => AllShow [] a
    ConsShow : Applicative f => Show (f (Tensor fs dtype)) => AllShow ((# f) :: fs) dtype

  public export
  genTensorShow : (allShow : AllShow shape a) => Tensor shape a -> String
  genTensorShow {allShow = NilShow} (GTZ val) = show val
  genTensorShow {allShow = ConsShow} (GTS xs) = show xs

  public export
  (allShow : AllShow shape a) => Show (Tensor shape a) where
    show = genTensorShow

namespace FunctorT
  public export
  Functor (Tensor shape) where
    map f (GTZ val) = GTZ $ f val
    map f (GTS xs) = GTS $ (map f) <$> xs


namespace ApplicativeTensorA
  ||| Unit of a monoidal functor
  public export
  tensorReplicate : {shape : Vect n ApplF} -> a -> Tensor shape a
  tensorReplicate {shape = []} a = GTZ a
  tensorReplicate {shape = ((# _) :: _)} a = GTS (pure (tensorReplicate a))
  
  ||| Generalised zip
  ||| Laxator of a monoidal functor
  public export
  liftA2Tensor : Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
  liftA2Tensor (GTZ a) (GTZ b) = GTZ (a, b)
  liftA2Tensor (GTS as) (GTS bs) = GTS $ (uncurry liftA2Tensor) <$> (liftA2 as bs)
  
  public export
  {shape : Vect n ApplF} -> Applicative (Tensor shape) where
    pure = tensorReplicate
    fs <*> xs = (uncurry ($)) <$> liftA2Tensor fs xs 



namespace NumericTensorA
  public export
  {shape : Vect n ApplF} -> Num a => Num (Tensor shape a) where
    fromInteger i = tensorReplicate (fromInteger i)
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys


  public export
  {shape : Vect n ApplF} -> Neg a => Neg (Tensor shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : Vect n ApplF} -> Abs a => Abs (Tensor shape a) where
    abs = (abs <$>)




namespace AlgebraTensorA
  public export
  data AllAlgebra : (shape : Vect n ApplF) -> (dtype : Type) -> Type where
    NilAlgebra : AllAlgebra [] a
    ConsAlgebra : Algebra f (Tensor fs a) => Applicative f
      => AllAlgebra fs a -> AllAlgebra ((# f) :: fs) a

  public export
  reduceTensor : {shape : Vect n ApplF} -> (allAlgebra : AllAlgebra shape a) => Tensor shape a -> a
  reduceTensor {allAlgebra = NilAlgebra} (GTZ val) = val
  reduceTensor {allAlgebra=(ConsAlgebra fx)} (GTS xs)
    = reduceTensor @{fx} (reduce xs)

  public export
  {shape : Vect n ApplF} -> (allAlgebra : AllAlgebra shape a) => Algebra (Tensor shape) a where
    reduce = reduceTensor


namespace FoldableTensorA

  public export
  data AllFoldable : (shape : Vect n ApplF) -> (dtype : Type) -> Type where
      NilFoldable : AllFoldable [] a
      ConsFoldable : Foldable f => Applicative f
        => f (Tensor ds dtype) -> AllFoldable ((# f) :: ds) dtype
  
  
  -- genTensorFoldable : {shape : Vect n ApplF} -> (allFoldable : AllFoldable shape a) => Foldable (Tensor shape)
  -- foldrGenFoldable : {shape : Vect n (ApplF [Functor, Foldable])} -> (f : a -> b -> b) -> (z : b) -> Tensor shape a -> b
  -- foldrGenFoldable f z (GTZ val) = f val z
  -- foldrGenFoldable f z (GTS xs) = foldr (\t, acc => foldr f acc t) z xs -- \t, acc => foldr f acc t should work but same problem as in Functor. Needs to be extracted to the type level...
  
  
  -- {shape : Vect n ApplF} -> (allFoldable : AllFoldable shape a) => Foldable (Tensor shape) where
  --    foldr = ?loooah


-- Dot product in the usual sense
public export
dot : {shape : Vect n ApplF} -> {a : Type}
  -> Num a => AllAlgebra shape a
  => Tensor shape a -> Tensor shape a -> Tensor [] a
dot xs ys = GTZ $ reduce $ (\(x, y) => x ~*~ y) <$> liftA2Tensor xs ys

-- public export
-- matMul : {a : Type}
--   -> (Num a, Algebra g (h a))
--   => Tensor [i, j] a -> Tensor [j, k] -> Tensor [i, k] a
-- matMul m1 m2 = m1 <&> (\row => multiplyVM row m2)

||| This recovers usual tensors in Tensor.Tensor
public export
Tensor : (shape : Vect n Nat) -> Type -> Type
Tensor shape = Tensor $ (\n => # (Vect n)) <$> shape

public export
GenArray : (shape : Vect rank ApplF) -> (dtype : Type) -> Type
GenArray [] dtype = dtype
GenArray ((# s) :: ss) dtype = s (GenArray ss dtype)

public export
fromGenArray : {shape : Vect rank ApplF} -> GenArray shape a -> Tensor shape a
fromGenArray {shape = []} a = GTZ a
fromGenArray {shape = ((# _) :: _)} t = GTS (fromGenArray <$> t)


-- TODO how to do indexing here? We'd need some notion of a shape and positions in a tree


{-
Hacking with Jules
preserves : {a : Type} -> (a -> Type) -> (a -> a) -> Type
preserves {a} c f = (x : a) -> (c x -> c (f x))

allShow : (shape : Vect n (Type -> Type)) -> Type
allShow shape = All (preserves Show) shape