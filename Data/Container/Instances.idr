module Data.Container.Instances

import Data.Fin
import Data.Vect


import Data.Container.Definition
import Data.Functor.Naperian
import Misc
import Data.Tree
import Algebra
import public Data.Container.TreeUtils -- rexport all the stuff inside


%hide Data.Vect.fromList


||| Examples
namespace MainContainerExamples
  ||| Container with a single thing
  public export
  Scalar : Cont
  Scalar = (_ : Unit) !> Unit

  ||| Product
  public export
  Pair : Cont
  Pair = (_ : Unit) !> Bool

  ||| Coproduct
  public export
  Either : Cont
  Either = (_ : Bool) !> Unit

  ||| +1  
  public export
  Maybe : Cont
  Maybe = (b : Bool) !> (if b then Unit else Void)
  
  public export
  List : Cont
  List = (n : Nat) !> (Fin n)
  
  ||| Container of n things 
  public export
  Vect : Nat -> Cont
  Vect n = (_ : Unit) !> Fin n

  ||| Container of an infinite number of things
  public export
  Stream : Cont
  Stream = (_ : Unit) !> Nat
  
  ||| Binary trees with data stored at nodes
  public export
  BTreeNode : Cont
  BTreeNode = (b : BTreeShape) !> FinBTreeNode b
  
  ||| Binary trees with data stored at leaves
  public export
  BTreeLeaf : Cont
  BTreeLeaf = (b : BTreeShape) !> FinBTreeLeaf b


namespace ExtensionsOfMainContainerExamples
  ||| Isomorphic to the Identity
  public export
  Scalar' : Type -> Type
  Scalar' = Ext Scalar

  ||| Isomorphic to Pair
  public export
  Pair' : Type -> Type
  Pair' = Ext Pair
  
  ||| Isomorphic to Either
  public export
  Either' : Type -> Type
  Either' = Ext Either

  ||| Isomorphic to Maybe
  public export
  Maybe' : Type -> Type
  Maybe' = Ext Maybe
  
  ||| Isomorphic to List
  public export
  List' : Type -> Type
  List' = Ext List

  ||| Isomorphic to Vect
  public export
  Vect' : (n : Nat) -> Type -> Type
  Vect' n x = (Vect n) `fullOf` x

  ||| Isomorphic to Stream
  public export
  Stream' : Type -> Type
  Stream' = Ext Stream

  
  ||| Isomorphic to Trees with data at only nodes
  public export
  BTreeNode' : Type -> Type
  BTreeNode' = Ext BTreeNode
  
  ||| Isomorphic to Trees with data only at leaves
  public export
  BTreeLeaf' : Type -> Type
  BTreeLeaf' = Ext BTreeLeaf

-- public export
-- Functor (Vect' n) where
--   map f a = map {f=(Ext (Vect n))} f a

-- public export
-- {n : Nat} -> Applicative (Vect' n) where
--   pure a = fromVect (pure a)
--   fs <*> vs = fromVect $ toVect fs <*> toVect vs 



namespace ConversionFunctions
  public export
  fromIdentity : a -> Scalar' a
  fromIdentity a = () <| (\_ => a)

  public export
  toIdentity : Scalar' a -> a
  toIdentity (() <| f) = f ()

  public export
  fromList : List x -> List' x
  fromList [] = (0 <| absurd)
  fromList (x :: xs) = let (l <| c) = fromList xs
                       in (S l <| addBeginning x c)

  public export
  toList : List' x -> List x
  toList (0 <| _) = []
  toList ((S k) <| ind) = let (x, c) = removeBeginning ind
                          in x :: toList (k <| c)
  
  
  public export
  fromVect : Vect n x -> Vect' n x
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n x -> Vect n x
  toVect (_ <| indexCont) = vectTabulate indexCont
  
  
  
  
  fromTreeHelper : FinBTreeNode LeafS -> a
  fromTreeHelper Root impossible
  fromTreeHelper (GoL x) impossible
  fromTreeHelper (GoR x) impossible
  
  public export
  fromBTreeNode : BTreeNode a -> BTreeNode' a
  fromBTreeNode (Leaf ()) = (LeafS <| fromTreeHelper)
  fromBTreeNode (Node node leftTree rightTree)
    = let (lts <| ltc) = fromBTreeNode leftTree
          (rts <| rtc) = fromBTreeNode rightTree
      in (NodeS lts rts <| \pos =>
            case pos of
              Root => node
              GoL posL => ltc posL
              GoR posR => rtc posR)

  public export
  toBTreeNode : BTreeNode' a -> BTreeNode a
  toBTreeNode (LeafS <| indexCont) = Leaf ()
  toBTreeNode ((NodeS lt rt) <| indexCont) = 
    Node (indexCont Root)
         (toBTreeNode (lt <| indexCont . GoL))
         (toBTreeNode (rt <| indexCont . GoR))
  
  public export
  fromBTreeLeaf : BTreeLeaf a -> BTreeLeaf' a
  fromBTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBTreeLeaf (Node node lt rt) =
    let (shL <| fnL) = fromBTreeLeaf lt
        (shR <| fnR) = fromBTreeLeaf rt
    in (NodeS shL shR <| \pos =>
          case pos of
            GoLLeaf posL => fnL posL
            GoRLeaf posR => fnR posR)

  public export
  toBTreeLeaf : BTreeLeaf' a -> BTreeLeaf a
  toBTreeLeaf (LeafS <| content) = Leaf (content AtLeaf)
  toBTreeLeaf ((NodeS l r) <| content) =
    Node' (toBTreeLeaf (l <| \posL => content (GoLLeaf posL)))
          (toBTreeLeaf (r <| \posR => content (GoRLeaf posR)))


public export
interface FromConcrete (cont : Cont) where
  constructor MkConcrete
  concreteType : Type -> Type
  concreteFunctor : Functor (concreteType)
  fromConcrete : concreteType a -> Ext cont a
  toConcrete : Ext cont a -> concreteType a

Functor Basics.id where
  map = id

public export
FromConcrete Scalar where
  concreteType = id
  concreteFunctor = %search
  fromConcrete = fromIdentity
  toConcrete = toIdentity

public export
FromConcrete List where
  concreteType = List
  concreteFunctor = %search -- TODO how to find the result of the search?
  fromConcrete = fromList
  toConcrete = toList

public export
{n : Nat} -> FromConcrete (Vect n) where
  concreteType = Vect n
  concreteFunctor = %search
  fromConcrete = fromVect
  toConcrete = toVect

public export
FromConcrete BTreeNode where
  concreteType = BTreeNode
  concreteFunctor = %search
  fromConcrete = fromBTreeNode
  toConcrete = toBTreeNode

public export
FromConcrete BTreeLeaf where
  concreteType = BTreeLeaf
  concreteFunctor = %search
  fromConcrete = fromBTreeLeaf
  toConcrete = toBTreeLeaf

namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Ext (Vect n) x) where
    v == v' = (toVect v) == (toVect v')
 
  public export
  {n : Nat} -> Show x => Show (Ext (Vect n) x) where
    show v = show (toVect v)

  public export
  {n : Nat} -> Foldable (Ext (Vect n)) where
    foldr f z v = foldr f z (toVect v)
  
  -- public export
  -- {n : Nat} -> Applicative (Ext (Vect n)) where
  --   pure a = fromVect $ pure a
  --   fs <*> vs = fromVect $ toVect fs <*> toVect vs

  public export
  {n : Nat} -> Num a => Algebra (Ext (Vect n)) a where
    reduce v = reduce (toVect v)

  -- TODO Naperian instance? Or is that covered by the one in Definiton.idr?


namespace BTreeLeafInstances

  showBTreeLeaf' : Show a => BTreeLeaf' a -> String
  showBTreeLeaf' (LeafS <| content) = "Leaf (" ++ show {ty=a} (content AtLeaf) ++ ")"
  showBTreeLeaf' ((NodeS l r) <| content) =
    let leftSubtree : BTreeLeaf' a = (l <| \posL => content (GoLLeaf posL))
        rightSubtree : BTreeLeaf' a = (r <| \posR => content (GoRLeaf posR))
    in "Node (" ++ showBTreeLeaf' leftSubtree ++ ") (" ++ showBTreeLeaf' rightSubtree ++ ")"

  partial -- not partial but not sure how to convince Idris totality checker
  public export
  Show a => Show (BTreeLeaf' a) where
    show t = show (toBTreeLeaf t)

  public export
  Eq a => Eq (BTreeLeaf' a) where
    (LeafS <| v) == (LeafS <| v') = v AtLeaf == v' AtLeaf
    ((NodeS l r) <| v) == ((NodeS l' r') <| v') =
      (l == l') && (r == r') && ?vnm -- Assuming Eq BTreeShape is defined elsewhere
    _ == _ = False

  public export
  liftA2BBTreeLeaf' : BTreeLeaf' a -> BTreeLeaf' b -> BTreeLeaf' (a, b)
  liftA2BBTreeLeaf' (LeafS <| v) (LeafS <| v') = LeafS <| (\x => (v x, v' x))
  liftA2BBTreeLeaf' (LeafS <| v) (NodeS l' r' <| v') =
    NodeS l' r' <| \pos =>
      case pos of
        GoLLeaf posL' => (v AtLeaf, v' (GoLLeaf posL'))
        GoRLeaf posR' => (v AtLeaf, v' (GoRLeaf posR'))
  liftA2BBTreeLeaf' (NodeS l r <| v) (LeafS <| v') =
    NodeS l r <| \pos =>
      case pos of
        GoLLeaf posL => (v (GoLLeaf posL), v' AtLeaf)
        GoRLeaf posR => (v (GoRLeaf posR), v' AtLeaf)
  liftA2BBTreeLeaf' (NodeS l r <| v) (NodeS l' r' <| v') =
    let (ls <| fl) = liftA2BBTreeLeaf' (l <| v . GoLLeaf) (l' <| v' . GoLLeaf)
        (rs <| fr) = liftA2BBTreeLeaf' (r <| v . GoRLeaf) (r' <| v' . GoRLeaf)
    in (NodeS ls rs <| \pos =>
         case pos of
           GoLLeaf posL => fl posL
           GoRLeaf posR => fr posR)

  public export
  Applicative BTreeLeaf' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BBTreeLeaf' fs vs 


  ||| Just summing up elements of the tree given by the Num a structure
  public export
  Num a => Algebra BTreeLeaf' a where
    reduce (LeafS <| v) = v AtLeaf
    reduce ((NodeS l r) <| v) =
      let leftSubtree = l <| \posL => v (GoLLeaf posL)
          rightSubtree = r <| \posR => v (GoRLeaf posR)
      in reduce {f=BTreeLeaf'} leftSubtree +
         reduce {f=BTreeLeaf'} rightSubtree


namespace BTreeNodeInstances
  -- TODO missing Eq instance for trees

  impossibleCase : FinBTreeNode LeafS -> (a, b)
  impossibleCase Root impossible
  impossibleCase (GoL x) impossible
  impossibleCase (GoR x) impossible

  ||| Combine two BTreeNode' structures, pairing values at corresponding nodes.
  ||| The resulting shape is the intersection of the input shapes.
  public export
  liftA2BTreeNode' : BTreeNode' a -> BTreeNode' b -> BTreeNode' (a, b)
  liftA2BTreeNode' ((NodeS l1 r1) <| f1) ((NodeS l2 r2) <| f2) =
    let (ls <| fl) = liftA2BTreeNode' (l1 <| f1 . GoL) (l2 <| f2 . GoL)
        (rs <| fr) = liftA2BTreeNode' (r1 <| f1 . GoR) (r2 <| f2 . GoR)

        resultFunc : FinBTreeNode (NodeS ls rs) -> (a, b)
        resultFunc Root = (f1 Root, f2 Root)
        resultFunc (GoL posL) = fl posL
        resultFunc (GoR posR) = fr posR
    in (NodeS ls rs <| resultFunc)
  liftA2BTreeNode' _ _ = LeafS <| impossibleCase

  public export
  Applicative BTreeNode' where
    pure a = NodeS LeafS LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BTreeNode' fs vs 

  public export
  Num a => Algebra BTreeNode' a where
    reduce (LeafS <| v) = fromInteger 0
    reduce ((NodeS l r) <| v) = v Root +
        reduce {f=BTreeNode'} (l <| v . GoL) +
        reduce {f=BTreeNode'} (r <| v . GoR)
  