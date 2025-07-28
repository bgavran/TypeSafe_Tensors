module Data.Tensor.Utils

import Data.List
import Data.Nat -- Add import for Cast
import System.Random


import Data.Tensor
import Data.Container.Morphism
import Data.Functor.Naperian -- needed for range
import Misc

public export
zerosA : Num a => {shape : ApplContList conts} -> TensorA shape a
zerosA = tensorReplicateA (fromInteger 0)

public export
zeros : Num a => {shape : List Nat} -> Tensor shape a
zeros = tensorReplicate (fromInteger 0)

public export
onesA : Num a => {shape : ApplContList conts} -> TensorA shape a
onesA = tensorReplicateA (fromInteger 1)

public export
ones : Num a => {shape : List Nat} -> Tensor shape a
ones = tensorReplicate (fromInteger 1)

public export
range : {n : Nat} -> Cast Nat a => Tensor [n] a
range {n} = fromArray $ cast . finToNat <$> positions {f=Vect n}

||| Number of elements in a cubical tensor
size : {shape : List Nat} -> (0 _ : Tensor shape a) -> Nat
size {shape} _ = prod shape


||| Flatten a non-cubical tensor into a list
||| Requires that we have Foldable on all the components
||| In general we won't know the number of elements of a non-cubical tensor at compile time
public export
flattenA : {shape : ApplContList conts} -> Foldable (TensorA shape) =>
  TensorA shape a -> List a
flattenA = toList

||| Flatten a cubical tensor into a vector
||| Number of elements is known at compile time
||| Can even be zero, if any of shape elements is zero
flatten : {shape : List Nat} ->
  Tensor shape a -> Vect (prod shape) a
flatten (ToCubicalTensor (TS ex)) = (\(TZ a) => a) <$> toVect ex

||| Maximum value in a tensor
maxA : {shape : ApplContList conts} -> Foldable (TensorA shape) => Ord a =>
  TensorA shape a -> Maybe a
maxA = maxInList . flattenA

||| Maximum value in a cubical tensor
max : {shape : List Nat} -> Ord a =>
  Tensor shape a -> Maybe a
max = maxA . FromCubicalTensor

-- Probably there's a faster way to do this
public export
{n : Nat} -> Random a => Random (Vect n a) where
  randomIO = sequence $ replicate n randomIO
  randomRIO (lo, hi) = sequence $ zipWith (\l, h => randomRIO (l, h)) lo hi

public export
{shape : List Nat} -> Random a => Random (Tensor shape a) where
  randomIO = map (fromArray . toArrayHelper) randomIO
  
  randomRIO (lo, hi) = do
    let loFlat = flatten lo
    let hiFlat = flatten hi
    randomVect <- randomRIO (loFlat, hiFlat)
    pure $ fromArray (toArrayHelper randomVect)

random : Random a => (shape : List Nat) -> IO (Tensor shape a)
random shape = randomIO

-- public export
-- eye : Num a => TensorA [n, n] a
-- eye = ?eye_rhs