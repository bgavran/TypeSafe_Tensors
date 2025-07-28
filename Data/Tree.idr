module Data.Tree

||| Finite binary trees with labels on leaves and nodes
||| Inductive definition
public export
data BTree : (leafType : Type) -> (nodeType : Type) -> Type where
    Leaf : (leaf : leafType)
        -> BTree leafType nodeType
    Node : (node : nodeType)
        -> (leftTree : BTree leafType nodeType)
        -> (rightTree : BTree leafType nodeType)
        -> BTree leafType nodeType

%name BTree bt, bt', bt''

public export
Leaf' : BTree () n
Leaf' = Leaf ()

public export
Node' : BTree l () -> BTree l () -> BTree l ()
Node' = Node ()

public export
Bifunctor BTree where
    bimap f g (Leaf x) = Leaf (f x)
    bimap f g (Node n leftTree rightTree)
      = Node (g n) (bimap f g leftTree) (bimap f g rightTree)

-- {leafType : Type} -> Applicative (\n => BTree leafType n) where
--     pure x = ?ooo
--     fs <*> xs = ?oii
    -- (Leaf f) <*> (Leaf x) = Leaf (f x)
    -- (Leaf f) <*> (Node n leftTree rightTree) = Node n (f <*> leftTree) (f <*> rightTree)
    -- (Node n leftTree rightTree) <*> (Leaf x) = Node n (leftTree <*> (Leaf x)) (rightTree <*> (Leaf x))
    -- (Node n leftTree rightTree) <*> (Node m v s) = Node n (leftTree <*> v) (rightTree <*> s)

public export
BTreeLeaf : (leafType : Type) -> Type
BTreeLeaf leafType = BTree leafType ()

public export
BTreeNode : (nodeType : Type) -> Type
BTreeNode nodeType = BTree () nodeType

namespace BTreeLeafInstances
  public export
  Show a => Show (BTreeLeaf a) where
    show (Leaf x) = "Leaf " ++ show x
    show (Node () leftTree rightTree)
      = "Node (" ++ show leftTree ++ ") (" ++ show rightTree ++ ")"

  public export
  Functor BTreeLeaf where
      map f (Leaf x) = Leaf (f x)
      map {a} {b} f (Node x leftTree rightTree)
        = Node x (map {f=BTreeLeaf} f leftTree) (map {f=BTreeLeaf} f rightTree)

  public export
  liftA2BTreeLeaf : BTreeLeaf a -> BTreeLeaf b -> BTreeLeaf (a, b)
  liftA2BTreeLeaf (Leaf a) (Leaf b) = Leaf (a, b)
  liftA2BTreeLeaf l@(Leaf x) (Node n z w)
    = Node n (liftA2BTreeLeaf l z) (liftA2BTreeLeaf l w)
  liftA2BTreeLeaf (Node n z w) (Leaf x)
    = Node n (liftA2BTreeLeaf z (Leaf x)) (liftA2BTreeLeaf w (Leaf x))
  liftA2BTreeLeaf (Node n y z) (Node m v s) = Node n (liftA2BTreeLeaf y v) (liftA2BTreeLeaf z s) -- there's a choice here on what node to use! Maybe if we had a dot there?

  public export
  Applicative BTreeLeaf where
      pure x = Leaf x
      fs <*> xs = map {f=BTreeLeaf} (uncurry ($)) $ liftA2BTreeLeaf fs xs 

  -- Is this even possible?
  -- probably is, but foldable really means traversing in a linear order
  -- with tree in principle we'd have to process each subtree in parallel
  -- but we could implement foldable by first making a choice on how to traverse a tree and turn it into a list, and then performing the fold on the resulting list
  public export
  Foldable BTreeLeaf where
    foldr f z (Leaf leaf) = f leaf z
    foldr f z (Node _ leftTree rightTree) = ?oo_1 where
      leftTreeRes : acc
      leftTreeRes = foldr {t=BTreeLeaf} f z leftTree
      rightTreeRes = foldr {t=BTreeLeaf} f z rightTree

namespace BTreeNodeInstances
  public export
  Functor BTreeNode where
    map f (Leaf leaf) = Leaf leaf -- only one element
    map f (Node node leftTree rightTree)
      = Node (f node) (map {f=BTreeNode} f leftTree) (map {f=BTreeNode} f rightTree) 


  -- Does this work only when the shapes match fully?
  public export
  liftA2BTreeNode : BTreeNode n -> BTreeNode m -> BTreeNode (n, m)
  liftA2BTreeNode (Node n lt rt) (Node m lt' rt') = Node (n, m) (liftA2BTreeNode lt lt') (liftA2BTreeNode rt rt')
  liftA2BTreeNode _ _ = Leaf ()

  public export
  Applicative BTreeNode where
    pure a = Leaf () -- Is this correct?
    fs <*> xs = map {f=BTreeNode} (uncurry ($)) $ liftA2BTreeNode fs xs 


namespace TreeRotation
  {-
  Can only rotate right trees of the shape

     /\
    /\ c
   a b

  Other shapes
    a
    or
    /\
    a b
     or

     /\
    a /\              --- here a could be a Leaf node, making this equal to the case above
      b c

  don't work
  -}
  public export
  data CanRotateRight : (BTree : BTreeLeaf a) -> Type where
    RotateRight : (leftLeftTree : BTreeLeaf a)
               -> (leftRightTree : BTreeLeaf a)
               -> (rightTree : BTreeLeaf a)
               -> CanRotateRight (Node' (Node' leftLeftTree leftRightTree) rightTree)


--  public export
--  cannotRotateLeaf : CanRotateRight (Leaf leaf) -> Void
--  cannotRotateLeaf (RotateRight _ _ _) impossible

--  public export
--   cannotRotateThisTree : CanRotateRight (Node n (Leaf l) (Node n' lt rt)) -> Void
--   cannotRotateThisTree (RotateRight _ _ _) impossible

  {-

     /\             /\   
    /\ c    -->    a /\
   a b               b c

  -}
  -- Tree rotation
  public export
  rotateRight : (tree : BTreeLeaf a)
             -> (CanRotateRight tree)
             -> BTreeLeaf a
  rotateRight (Node n (Node n' leftLeftTree leftRightTree) rightTree) x
    = Node n leftLeftTree (Node n' leftRightTree rightTree)





  PathBTree : Type
  PathBTree = List Bool


  -- Swap the left and right subtrees at at specified path
  commute : PathBTree -> BTreeLeaf l -> BTreeLeaf l
  commute [] (Leaf leaf) = Leaf leaf
  commute [] (Node node l r) = Node node r l
  commute (x :: xs) (Leaf leaf) = Leaf leaf
  commute (False :: xs) (Node node l r) = Node node (commute xs l) r
  commute (True :: xs) (Node node l r) = Node node l (commute xs r)
