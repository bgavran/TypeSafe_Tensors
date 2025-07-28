module Algebra

import Data.Vect

import Data.Tree
import Misc


||| Generalised sum operation
||| Categorically, an F-Algebra
public export
interface Algebra (f : Type -> Type) a where
  constructor MkAlgebra
  reduce : f a -> a

public export
Num a => Algebra List a where
  reduce = foldr (+) (fromInteger 0)

-- Does this work for any Applicative? I think not, because in trees we have to choose an order of summation. But that might not impact things?
public export
{n : Nat} -> Num a => Algebra (Vect n) a where
  reduce = foldr (+) (fromInteger 0)

-- public export
-- [appSum] {shape : Vect n Nat} -> 
-- Num a => Applicative f =>
-- Algebra (TensorA shape) (f a) using applicativeNum where
--   reduce (TZ val) = val
--   reduce (TS xs) = reduce (reduce <$> xs)
-- 
-- aa : Algebra (TensorA [2]) (TensorA [3] a) => a
-- aa = ?aa_rhs

||| Just summing up elements of the tree given by the Num a structure
public export
Num a => Algebra BTreeLeaf a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BTreeLeaf} leftTree) + 
      (reduce {f=BTreeLeaf} rightTree)

-- can be simplified by uncommenting the Num (f a) instance in Num.idr
public export
[usualSum'] Num a => Applicative f => Algebra BTreeLeaf (f a) where
  reduce (Leaf leaf) = leaf
  reduce (Node node leftTree rightTree)
    = let lt = reduce {f=BTreeLeaf} leftTree 
          rt = reduce {f=BTreeLeaf} rightTree
      in (uncurry (+)) <$> (liftA2 lt rt) 

public export
Num a => Algebra BTreeNode a where
  reduce (Leaf _) = fromInteger 0
  reduce (Node node leftTree rightTree)
     = node + (reduce {f=BTreeNode} leftTree)
            + (reduce {f=BTreeNode} rightTree)
