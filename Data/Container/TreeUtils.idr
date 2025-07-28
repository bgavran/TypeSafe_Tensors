module Data.Container.TreeUtils

||| Shapes of binary trees
public export
data BTreeShape : Type where
  LeafS : BTreeShape
  NodeS : BTreeShape -> BTreeShape -> BTreeShape

public export
numLeaves : BTreeShape -> Nat
numLeaves LeafS = 1
numLeaves (NodeS lt rt) = numLeaves lt + numLeaves rt

public export
Eq BTreeShape where
  LeafS == LeafS = True
  NodeS l r == NodeS l' r' = l == l' && r == r'
  _ == _ = False


||| Positions corresponding to internal nodes within a BTreeShape shape.
public export
data FinBTreeNode : (b : BTreeShape) -> Type where
  Root : {l, r : BTreeShape} -> FinBTreeNode (NodeS l r)
  GoL  : {l, r : BTreeShape} -> FinBTreeNode l -> FinBTreeNode (NodeS l r)
  GoR  : {l, r : BTreeShape} -> FinBTreeNode r -> FinBTreeNode (NodeS l r)

||| Positions corresponding to leaves within a BTreeShape shape.
public export
data FinBTreeLeaf : (b : BTreeShape) -> Type where
  AtLeaf : FinBTreeLeaf LeafS
  GoLLeaf : {l, r : BTreeShape} -> FinBTreeLeaf l -> FinBTreeLeaf (NodeS l r)
  GoRLeaf : {l, r : BTreeShape} -> FinBTreeLeaf r -> FinBTreeLeaf (NodeS l r)
