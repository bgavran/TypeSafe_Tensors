module Data.Tensor

import Data.DPair
import public Data.Fin
import public Data.Vect
import public Data.List
import Data.Fin.Arith
import public Data.List.Quantifiers

import public Data.Container.Definition
import public Data.Container.Instances
import public Data.Container.Morphism
import public Data.Container.Applicative
import public Algebra
import public Data.Tree
import public Misc
import Data.Functor.Naperian

%hide Builtin.infixr.(#)

{-----------------------------------------------------------
{-----------------------------------------------------------
This file defines the main 'applicative tensor' type
Together with functionality for useful working with them,
convenience functions, interfaces,...
-----------------------------------------------------------}
-----------------------------------------------------------}

||| Applicative tensors
||| Tensors whose shape is a list of applicative containers
public export
data TensorA : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> TensorA [] dtype
    TS : Applicative (c `fullOf`) => {cs : ApplContList conts} ->
      c `fullOf` (TensorA cs dtype) -> TensorA (c :: cs) dtype

%name TensorA t, t'

public export
ScalarA : (dtype : Type) -> Type
ScalarA dtype = TensorA [] dtype

public export
VectorA : (length : ApplC) -> (dtype : Type) -> Type
VectorA (# length) dtype = TensorA [length] dtype

public export
MatrixA : (row, col : ApplC) -> (dtype : Type) -> Type
MatrixA (# row) (# col) dtype = TensorA [row, col] dtype


-----------------
-- ArrayA
-----------------

--   public export
--   data AllShow : (shape : ApplContList conts) -> (dtype : Type) -> Type where
--     NilShow : Show dtype => AllShow [] dtype
--     ConsShow : {c : Cont} -> {cs : ApplContList conts} ->
--       Applicative (Ext c) =>
--       Show (c `fullOf` (TensorA cs dtype)) =>
--       AllShow (c :: cs) dtype

public export
data AllConcrete : (shape : ApplContList conts) -> (dtype : Type) -> Type where
  NilConcrete : AllConcrete [] dtype
  ConsConcrete : {c : Cont} -> {cs : ApplContList conts} -> 
    Applicative (Ext c) =>
    (fr : FromConcrete c) =>
    (afr : AllConcrete cs dtype) =>
    AllConcrete (c :: cs) dtype


||| Convenience function for constructing a TensorA
||| The input is a nested list of containers with a FromConcrete instance
||| Meaning that they're matched to a concrete inductively defined Idris type
public export
ArrayA : (shape : ApplContList conts) ->
  (dtype : Type) ->
  (concr : AllConcrete shape dtype) =>
  Type
ArrayA [] dtype = dtype
ArrayA (c :: cs) {concr = ConsConcrete {fr}} dtype
  = concreteType @{fr} (ArrayA cs dtype)


public export
fromArrayA : {shape : ApplContList conts} ->
  (concr : AllConcrete shape dtype) =>
  ArrayA shape dtype -> TensorA shape dtype
fromArrayA {shape = []} x = TZ x
fromArrayA {shape = (_ :: _)} {concr = ConsConcrete {fr = (MkConcrete f concreteFunctor fromConcrete _)}} xs = TS $ fromConcrete $ fromArrayA <$> xs

public export
toArrayA : {shape : ApplContList conts} ->
  (concr : AllConcrete shape dtype) =>
  TensorA shape dtype -> ArrayA shape dtype
toArrayA (TZ val) = val
toArrayA {concr = ConsConcrete {fr = (MkConcrete f concreteFunctor _ toConcrete)} {afr} } (TS xs) = toConcrete $ toArrayA {concr=afr} <$> xs


-----------------
-- Composition product
-- TensorA defined above can be thought of as a composition (in the composition of containers) of applicative containers defining its shape
-----------------

public export
fromTensorA : {conts : List ApplC} -> {shape : ApplContList conts} ->
  TensorA shape a -> Ext (ComposeContainers conts) a
fromTensorA {shape = []} (TZ val) = () <| \_ => val
fromTensorA {shape = (c :: cs)} (TS ex)
  = let (cs' <| index') = fromTensorA {shape=cs} <$> ex
    in (cs' <| shapeExt . index') <| uncurry (\x => indexCont (index' x))

public export
toTensorA : {conts : List ApplC} -> {shape : ApplContList conts} ->
  (ComposeContainers conts) `fullOf` a -> TensorA shape a
toTensorA {shape = []} (() <| indexCont) = TZ (indexCont ())
toTensorA {shape = (c :: cs)} ((cshTerm <| cposTerm) <| indexCont)
  = TS $ cshTerm <| \d => toTensorA $ cposTerm d <| curry indexCont d


||| General, dependent-lens based applicative tensor reshaping
||| Also should capture views, traversals, and other that don't touch content 
public export
reshapeTensorA : {contsOld, contsNew : List ApplC} ->
  {oldShape : ApplContList contsOld} -> {newShape : ApplContList contsNew} ->
  (ComposeContainers contsOld =%> ComposeContainers contsNew) ->
  TensorA oldShape a -> TensorA newShape a
reshapeTensorA dLens = toTensorA . (contMapExt dLens) . fromTensorA
    

namespace EqTensorA
  public export
  data AllEq : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    NilEq : Eq dtype => AllEq [] dtype
    ConsEq : {c : Cont} -> {cs : ApplContList conts} ->
      (applExtc : Applicative (Ext c)) =>
      (eqCont: Eq (c `fullOf` (TensorA cs dtype))) =>
      AllEq (c :: cs) dtype

  public export
  tensorEq : {shape : ApplContList conts} -> (allEq : AllEq shape dtype) =>
    TensorA shape dtype -> TensorA shape dtype -> Bool
  tensorEq {allEq = NilEq} (TZ val) (TZ val') = val == val'
  tensorEq {allEq = ConsEq} (TS xs) (TS xs') = xs == xs'

  public export
  {shape : ApplContList conts} -> (allEq : AllEq shape dtype) =>
    Eq (TensorA shape dtype) where
      (==) = tensorEq



namespace ShowTensorA
  public export
  data AllShow : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    NilShow : Show dtype => AllShow [] dtype
    ConsShow : {c : Cont} -> {cs : ApplContList conts} ->
      Applicative (Ext c) =>
      Show (c `fullOf` (TensorA cs dtype)) =>
      AllShow (c :: cs) dtype

  ||| TODO this works, but we need to actually implement pretty printing
  public export
  tensorShow : {shape : ApplContList conts} -> (allShow : AllShow shape dtype) =>
    TensorA shape dtype -> String
  tensorShow {allShow = NilShow} (TZ val) = show val
  tensorShow {allShow = ConsShow} (TS xs) = show xs

  public export
  {shape : ApplContList conts} ->
  (allShow : AllShow shape dtype) =>
    Show (TensorA shape dtype) where
      show = tensorShow

namespace FunctorTensorA
  public export
  Functor (TensorA shape) where
    map f (TZ val) = TZ $ f val
    map f (TS xs) = TS $ (map f) <$> xs


namespace ApplicativeTensorA
  ||| Datatype for witnessing that all the containers in a shape are applicative
  -- public export -- Not used below since Applicative is baked in to TensorA
  -- data AllApplicative : (shape : Vect n Cont) -> Type where
  --   Nil : AllApplicative []
  --   Cons : Applicative (Ext c) => AllApplicative cs -> AllApplicative (c :: cs)

  ||| Unit of the monoidal functor
  public export
  tensorReplicateA : {shape : ApplContList conts}
    -> a -> TensorA shape a
  tensorReplicateA {shape = []} a = TZ a
  tensorReplicateA {shape = (c :: cs)} a = TS $ pure (tensorReplicateA a)

  ||| Laxator of the monoidal functor
  public export
  liftA2TensorA : {shape : ApplContList conts} ->
    TensorA shape a -> TensorA shape b -> TensorA shape (a, b)
  liftA2TensorA (TZ a) (TZ b) = TZ (a, b)
  liftA2TensorA (TS x) (TS y) = TS $ uncurry liftA2TensorA <$> (liftA2 x y)

  public export
  {shape : ApplContList conts} -> Applicative (TensorA shape) where
    pure = tensorReplicateA 
    fs <*> xs = uncurry ($) <$> liftA2TensorA fs xs 

namespace NumericTensorA
  public export
  {shape : ApplContList conts} -> Num a => Num (TensorA shape a) where
    fromInteger i = pure (fromInteger i)
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys

  public export
  {shape : ApplContList conts} -> Neg a => Neg (TensorA shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : ApplContList conts} -> Abs a => Abs (TensorA shape a) where
    abs = (abs <$>)

  public export
  {shape : ApplContList conts} -> Fractional a => Fractional (TensorA shape a) where
    t / v = (uncurry (/)) <$> liftA2 t v

  public export
  {shape : ApplContList conts} -> Exp a => Exp (TensorA shape a) where
    exp = (exp <$>)



namespace AlgebraTensorA
  public export
  data AllAlgebra : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    Nil : AllAlgebra [] a
    (::) : {c : Cont} -> {cs : ApplContList conts} ->
      Applicative (Ext c) =>
      (alg : Algebra (Ext c) (TensorA cs a)) =>
      (allAlg : AllAlgebra cs a) => AllAlgebra (c :: cs) a

  public export
  reduceTensorA : {shape : ApplContList conts} -> (allAlgebra : AllAlgebra shape a) => TensorA shape a -> a
  reduceTensorA {allAlgebra = []} (TZ val) = val
  reduceTensorA {allAlgebra = ((::) {allAlg=cs})} (TS xs) = reduceTensorA @{cs} (reduce xs)


  public export
  {shape : ApplContList conts} ->
  (allAlgebra : AllAlgebra shape a) =>
  Algebra (TensorA shape) a where
    reduce = reduceTensorA

  public export
  [appSumTensorA] {shape : ApplContList conts} ->
    {a : Type} ->
    Num a =>
    Applicative (Ext c) =>
    (allAlg : AllAlgebra shape a) =>
    Algebra (TensorA shape) ((Ext c) a) where
      reduce {allAlg = []} (TZ val) = val
      reduce {shape=(c::cs)} {allAlg = ((::) {allAlg=alg})} (TS xs) -- = ?fvhvh_2
        = let t = reduce {f=(TensorA cs)} <$> xs
          in ?ghhh -- reduce (reduce <$> xs)


namespace FoldableTensorA

  public export
  data AllFoldable : (shape : ApplContList conts) -> Type where
      NilFoldable : AllFoldable []
      ConsFoldable : {c : Cont} -> {cs : ApplContList conts} ->
        Foldable (Ext c) =>
        Applicative (Ext c) =>
        AllFoldable cs ->
        AllFoldable (c :: cs)


  public export
  tensorFoldrA : (allFoldable : AllFoldable shape) =>
    (el -> acc -> acc) -> acc -> TensorA shape el -> acc
  tensorFoldrA {allFoldable = NilFoldable} f z (TZ val) = f val z
  tensorFoldrA {allFoldable = (ConsFoldable recAllFoldable)} f z (TS xs) =
      foldr (\t, acc => tensorFoldrA {allFoldable=recAllFoldable} f acc t) z xs

  public export
  {conts : List ApplC} ->
  {shape : ApplContList conts} ->
  (allFoldable : AllFoldable shape) =>
  Foldable (TensorA shape) where
    foldr = tensorFoldrA


namespace TensorAContractions
  public export
  dotA : {shape : ApplContList conts} -> {a : Type} -> Num a =>
    Algebra (TensorA shape) a =>
    TensorA shape a -> TensorA shape a -> TensorA [] a
  dotA xs ys = TZ $ reduce $ (\(x, y) => x * y) <$> liftA2TensorA xs ys


  -- Multiply a matrix and a vector
  public export
  matrixVectorProductA : {a : Type} -> Num a =>
    Applicative (Ext f) => Applicative (Ext g) =>
    AllAlgebra [g] a =>
    TensorA [f, g] a -> TensorA [g] a -> TensorA [f] a
  matrixVectorProductA (TS m) v = TS (dotA v <$> m)

  -- Multiply a vector and a matrix
  public export
  vectorMatrixProductA : {a : Type} -> {f, g : Cont} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    (allAlgebra : AllAlgebra [f, g] a) =>
    TensorA [f] a -> TensorA [f, g] a -> TensorA [g] a
  vectorMatrixProductA {allAlgebra = (::)} (TS v) (TS m)
    = let t = liftA2 v m
          w = (\((TZ val), v') => (val *) <$> v') <$> t
      in reduce {f=(Ext f)} w

  -- ij,jk->ik
  public export
  matMulA : {f, g, h : Cont} -> {a : Type} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    Applicative (Ext h) =>
    (allAlgebra : AllAlgebra [g, h] a) =>
    TensorA [f, g] a -> TensorA [g, h] a -> TensorA [f, h] a
  matMulA (TS m1) m2 = TS $ m1 <&> (\row => vectorMatrixProductA row m2)

  -- ij,kj->ki
  public export
  matrixMatrixProductA : {f, g, h : Cont} -> {a : Type} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    Applicative (Ext h) =>
    (allAlgebra : AllAlgebra [g] a) =>
    TensorA [f, g] a -> TensorA [h, g] a -> TensorA [h, f] a
  matrixMatrixProductA m (TS n) = TS (matrixVectorProductA m <$> n)





namespace NestedTensorAStuff
  public export
  toNestedTensorA : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  toNestedTensorA (TS vs) = TS (TZ <$> vs)

  public export infix 4 <-$

  public export
  (<-$) : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  (<-$) = toNestedTensorA

  public export
  fromNestedTensorA : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  fromNestedTensorA (TS vs) = TS $ (\(TZ jk) => jk) <$> vs

  public export infixr 4 $->
  public export
  ($->) : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  ($->) = fromNestedTensorA

  public export
  tensorMapFirstAxisA : {rest : Cont}
    -> {s1, s2 : ApplContList conts}
    -> Applicative (Ext rest)
    => (f : TensorA s1 a -> TensorA s2 a)
    -> TensorA (rest :: s1) a -> TensorA (rest :: s2) a
  tensorMapFirstAxisA f t = fromNestedTensorA $ map f $ toNestedTensorA t


  public export infixr 4 <-$->

  ||| Map, but for nested tensors
  public export
  (<-$->) : {rest : Cont}
    -> {shape : ApplContList conts}
    -> Applicative (Ext rest)
    => (f : TensorA shape a -> TensorA shape a)
    -> TensorA (rest :: shape) a -> TensorA (rest :: shape) a
  (<-$->) = tensorMapFirstAxisA



namespace CubicalTensor
  {-
  -----------------------------------------------------------

  public export
  Tensor' : (shape : List Nat) -> Type -> Type
  Tensor' shape = TensorA (NatsToApplConts shape)

  public export
  {shape : List Nat} ->
  AllEq (NatsToApplConts shape) a =>
  Eq (Tensor' shape a) where
    (==) = tensorEq

  public export
  {shape : List Nat} ->
  AllShow (NatsToApplConts shape) a =>
  Show (Tensor' shape a) where
    show = tensorShow

  public export
  {shape : List Nat} ->
  Num a =>
  Num (Tensor' shape a) where
    fromInteger i = fromInteger i
    t + t' = t + t'
    t * t' = t * t'

  {-
  TODO neg, abs, exp
   -}

  public export
  Functor (Tensor' shape) where
    map = map

  public export
  {shape : List Nat} ->
  Applicative (Tensor' shape) where
    pure = tensorReplicateA
    fs <*> xs = uncurry ($) <$> liftA2TensorA fs xs

  public export
  Array' : (shape : List Nat) -> (dtype : Type) -> Type
  Array' [] dtype = dtype
  Array' (s :: ss) dtype = Vect s (Array' ss dtype)
    

  public export
  fromArray' : {shape : List Nat} -> Array' shape a -> Tensor' shape a
  fromArray' {shape = []} x = TZ x
  fromArray' {shape = (s :: ss)} x = TS $ fromVect $ fromArray' <$> x


  public export
  ToCubicalTensor' : {shape : List Nat} ->
    TensorA (NatsToApplConts shape) a -> Tensor' shape a
  -- ToCubicalTensor' t = ToCubicalTensor t
  ToCubicalTensor' t = ?ToCubicalTensor'_rhs
  -}

  -- This recovers usual tensors in Tensor.Tensor

  -- public export infixr 5 +++
  -- public export
  -- (+++) : {cs : Vect n ApplC} -> {ds : Vect m ApplC}
  --   -> ApplContList cs -> ApplContList ds -> ApplContList (cs ++ ds)
  -- [] +++ ys = ys
  -- (c :: cs) +++ ys = c :: (cs +++ ys)


  -- vvv : (shape : Vect n Nat) -> Vect n ApplC
  -- vvv shape = (\n => # (Vect n)) <$> shape


  ||| This is a helper datatype for cubical tensors, i.e. those made only out of Vect
  ||| It allows specifying a tensor only by the size of the content, and is needed (instead of Tensor') to aid type inference
  ||| There might be a more ergonomic way to do this
  public export
  record Tensor (shape : List Nat) a where
    constructor ToCubicalTensor
    -- FromCubicalTensor : TensorA (NatsToApplConts shape) a
    FromCubicalTensor : TensorA (FlatStorage shape) a

  -- public export
  -- data TensorView : (shape : List Nat) -> (a : Type) -> Type where
  --     FlatTensor : {shape : List Nat} -> TensorA (FlatStorage shape) a -> Tensor shape a
  --     NonFlatTensor : {shape : List Nat} -> TensorA (NatsToApplConts shape) a -> Tensor shape a

  -- public export
  -- reshapeView : {oldShape, newShape : List Nat} ->
  --   {auto prf : prod newShape = prod oldShape} ->
  --   TensorView oldShape a ->
  --   TensorView newShape a
  -- reshapeView {prf} (MkTensorView flatData)
  --   = MkTensorView $ rewrite prf in flatData

  -- TODO we also have, what? 
  -- index, slice, take

  namespace TensorInterfaces
    public export
    {shape : List Nat} ->
    AllEq (FlatStorage shape) a =>
    Eq (Tensor shape a) where
        (ToCubicalTensor t) == (ToCubicalTensor t') = tensorEq t t'

    public export
    {shape : List Nat} ->
    AllShow (FlatStorage shape) a =>
    Show (Tensor shape a) where
      show (ToCubicalTensor t) = show t

    public export
    {shape : List Nat} ->
    Num a =>
    Num (Tensor shape a) where
      fromInteger i = ToCubicalTensor $ fromInteger {ty=(TensorA (FlatStorage shape) a)} i
      (ToCubicalTensor xs) + (ToCubicalTensor ys) = ToCubicalTensor $ (+) {ty=(TensorA (FlatStorage shape) a)} xs ys
      (ToCubicalTensor xs) * (ToCubicalTensor ys) = ToCubicalTensor $ (*) {ty=(TensorA (FlatStorage shape) a)} xs ys

    public export
    {shape : List Nat} ->
    Neg a =>
    Neg (Tensor shape a) where
      negate (ToCubicalTensor t) = ToCubicalTensor $ negate t
      (ToCubicalTensor xs) - (ToCubicalTensor ys) = ToCubicalTensor $ (-) {ty=(TensorA (FlatStorage shape) a)} xs ys

    public export
    {shape : List Nat} -> Abs a => Abs (Tensor shape a) where
      abs (ToCubicalTensor t) = ToCubicalTensor $ abs t

    public export
    Functor (Tensor shape) where
      map f (ToCubicalTensor t) = ToCubicalTensor $ map f t


    public export
    tensorReplicate : {shape : List Nat}
      -> a -> Tensor shape a
    tensorReplicate = ToCubicalTensor . tensorReplicateA

    liftA2Tensor : {shape : List Nat} -> Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
    liftA2Tensor (ToCubicalTensor xs) (ToCubicalTensor ys)
      = ToCubicalTensor (liftA2TensorA xs ys)

    public export
    {shape : List Nat} ->
    Applicative (Tensor shape) where
      pure = tensorReplicate
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs


    public export
    {shape : List Nat} ->
    AllAlgebra (FlatStorage shape) a =>
    Algebra (Tensor shape) a where
        reduce (ToCubicalTensor t) = reduce t

    -- public export
    -- tensorFoldrA : {shape : List Nat} ->
    --   (el -> acc -> acc) -> acc -> TensorA (FlatStorage shape) el -> acc
    -- tensorFoldrA f z t = ?aoooo
    -- tensorFoldrA {shape = []} f z t = foldr f z t
    -- tensorFoldrA {shape = (s :: ss)} f z (TS xs)
    --   = foldr (\t, acc => tensorFoldrA f acc t) z xs


    public export
    {shape : List Nat} ->
    Foldable (Tensor shape) where
      foldr f z (ToCubicalTensor t) = tensorFoldrA f z t

    -- TODO implement Traversable for TensorA, and then port it here
    -- public export
    -- tensorTraverseA : {shape : List Nat} -> Applicative f =>
    --   (a -> f b) -> TensorA (FlatStorage shape) a -> f (TensorA (FlatStorage shape) b)
    -- tensorTraverseA {shape = []} fn (TZ val) = TZ <$> fn val
    -- tensorTraverseA {shape = (s :: ss)} fn (TS xs)
    --   = TS <$> (fromVect <$> traverse (tensorCTraverse fn) (toVect xs))

    -- public export
    -- {shape : List Nat} ->
    -- Traversable (Tensor shape) where
    --   traverse f (ToCubicalTensor t) = ToCubicalTensor <$> tensorTraverseA f t

  public export
  dot : {shape : List Nat} -> {a : Type}
    -> Num a => AllAlgebra (FlatStorage shape) a
    => Tensor shape a -> Tensor shape a -> Tensor [] a
  dot (ToCubicalTensor v) (ToCubicalTensor w)
    = pure $ reduce $ (\(x, y) => x * y) <$> liftA2TensorA v w
    -- = let tt = dotA (FromCubicalTensor v) (FromCubicalTensor w)
    --   in ToCubicalTensor ?tuuu

  public export
  Array : (shape : List Nat) -> (dtype : Type) -> Type
  Array [] dtype = dtype
  Array (s :: ss) dtype = Vect s (Array ss dtype)

  -- public export
  -- fromArrayHelper : {shape : List Nat}
  --   -> Array shape a
  --   -> TensorA (FlatStorage shape) a
  -- fromArrayHelper {shape=[]} a = TS $ () <| (\_ => TZ a)
  -- fromArrayHelper {shape=(s :: ss)} t =
  --   let tt = fromArrayA 
  --   in TS $ () <| ?vnn

  public export
  fromArrayHelper : {shape : List Nat} ->
    Array shape a -> Vect (prod shape) a
  fromArrayHelper {shape = []} a = [a]
  fromArrayHelper {shape = (s :: ss)} a = concat (fromArrayHelper <$> a)

  public export
  toArrayHelper : {shape : List Nat} -> Vect (prod shape) a -> Array shape a
  toArrayHelper {shape = []} [a] = a
  toArrayHelper {shape = (s :: ss)} xs = toArrayHelper <$> (unConcat xs)

  public export
  fromArray : {shape : List Nat} -> Array shape a -> Tensor shape a
  fromArray = ToCubicalTensor . fromArrayA . fromArrayHelper

  public export
  toArray : {shape : List Nat} -> Tensor shape a -> Array shape a
  toArray = toArrayHelper . toArrayA . FromCubicalTensor

  public export
  reshape : {oldShape : List Nat} ->
    Tensor oldShape a ->
    {shape : List Nat} ->
    {auto prf : prod oldShape = prod shape} ->
    Tensor shape a
  reshape t = ToCubicalTensor $ reshapeTensorA
    (cubicalTensorToFlat %>> dLensProductReshape %>> flatToCubicalTensor) $
    FromCubicalTensor t

namespace IndexTensor
  -- public export
  -- data IndexTData : Type where
  --   NonCubical : (shape : ApplContList conts) -> IndexTData
  --   Cubical : (shape : Vect n Nat) -> IndexTData -- assuming every Naperian functor has shape=Fin d for some d, this describes Naperian TensorAs

  -- vnn : IndexTData -> Type -> Type
  -- vnn (NonCubical shape) = TensorA shape
  -- vnn (Cubical shape) = \_ => Unit

  -- -- vnnn : (conts : Vect n ApplC) -> Cont
  -- -- vnnn conts = foldr ?acc CUnit (GetC <$> conts)

  -- ||| TensorAs too are a container
  -- tensorCont : Type -> Cont
  -- tensorCont dtype = (s : IndexTData) !> vnn s
    
  ||| Machinery for indexing into a TensorA
  ||| It depends on shape, but also on the tensor t itself
  ||| This dependency is not needed for cubical tensors
  ||| TODO remove this dependence for cubical tensors
  public export
  data IndexTA :
    (shape : ApplContList conts) ->
    (t : TensorA shape dtype) -> Type where
    Nil : {val : dtype} -> IndexTA [] (TZ val)
    (::) :  {e : ((!>) shp' pos') `fullOf` (TensorA cs dtype)} -> 
      Applicative (Ext ((!>) shp' pos')) =>
      (p : pos' (shapeExt e)) ->
      IndexTA cs (indexCont e p) -> 
      IndexTA ((!>) shp' pos' :: cs) (TS e)

  public export
  indexTensorA : (t : TensorA shape a)
              -> (index : IndexTA shape t)
              -> a
  indexTensorA (TZ val) [] = val
  indexTensorA (TS xs) (i :: is) = indexTensorA (indexCont xs i) is 

  namespace CubicalIndex
    public export
    strides : (shape : List Nat) -> List Nat
    strides [] = []
    strides (s :: ss) = prod ss :: strides ss

    ||| It will be important to prove later that if all elements of shape are non-zero, then the head of the strides is also non-zero
    public export
    stridesProofHeadNonZero : {shape : List Nat} ->
      {auto prf : All IsSucc shape} ->
      {auto _ : NonEmpty (strides shape)} ->
      IsSucc (head (strides shape))
    stridesProofHeadNonZero {shape = (_ :: ss)} {prf = (_ :: ps)}
      = allSuccThenProdSucc ss
  
    ||| Index of a cubical tensor given a shape
    ||| This is 0-based indexing
    public export
    data IndexT : (shape : List Nat) -> Type where
      Nil  : IndexT []
      (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

    ||| Maybe Index of a cubical tensor given a shape
    ||| This is 0-based indexing
    public export
    data MIndexT : (shape : List Nat) -> Type where
      MNil  : MIndexT []
      (:::) : Maybe (Fin m) -> MIndexT ms -> MIndexT (m :: ms)

    mIndexToShape : {shape : List Nat} -> MIndexT shape -> List Nat
    mIndexToShape {shape = []} MNil = []
    mIndexToShape {shape = (s :: ss)} (Nothing ::: is) = s :: mIndexToShape is
    mIndexToShape ((Just i) ::: is) = finToNat i :: mIndexToShape is
  
    ||| Given a shape and an index, compute the index in the flattened tensor
    public export
    indexCount : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
      IndexT shape -> Fin (prod shape)
    indexCount {shape = []} _ = FZ
    indexCount {shape = (s :: ss)} {allNonZero = (_ :: ps)} (i :: is)
      = let restCount = indexCount is
            restCountWeakened = weakenMultN s restCount
            
            strideHeadNonZero = stridesProofHeadNonZero {shape=(s :: ss)} 
            hereCount = shiftMul (head (strides (s :: ss))) i
        in addFinsBounded hereCount restCountWeakened

  -- ideally we'd remove the allNonZero consraint in the future, but it shouldn't impact things too much for now
  public export
  indexTensor : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
    (t : Tensor shape a) ->
    (ind : IndexT shape) ->
    a
  indexTensor (ToCubicalTensor (TS v)) ind
    = let (TZ a) = index (indexCount ind) (toVect v)
      in a


  -- Why can't I use @ here?
  public export infixr 9 @@ -- for non-cubical tensors
  public export infixr 9 @@@ -- for cubical tensors

  public export
  (@@) : (t : TensorA shape a) -> IndexTA shape t -> a
  (@@) = indexTensorA

  public export
  (@@@) : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
    (t : Tensor shape a) ->
    (ind : IndexT shape) ->
    a
  (@@@) = indexTensor


namespace SliceTensor
  ||| Machinery for slicing cubical tensors
  ||| Crucially, different from the indexing one in the definition of (::)
  ||| Here we have Fin (S m) instead of Fin m
  public export
  data SliceT : (shape : List Nat) -> Type where
    Nil : SliceT []
    (::) : Fin (S m) -> SliceT ms -> SliceT (m :: ms)

  ||| Computes the shape of the tensor after the slicing
  public export
  sliceToShape : {shape : List Nat} -> SliceT shape -> List Nat
  sliceToShape Nil = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  -- analogus to take in Data.Vect, but for Fin
  public export 
  takeFinVect' : {n : Nat} ->
    (s : Fin (S n)) -> Vect' n a -> Vect' (finToNat s) a
  takeFinVect' s x = fromVect (takeFin s (toVect x))

  public export --
  takeTensor : {shape : List Nat} ->
    (slice : SliceT shape) ->
    Tensor shape a ->
    Tensor (sliceToShape slice) a
  -- takeTensor [] (ToCubicalTensor (TZ val)) = ToCubicalTensor (TZ val)
  -- takeTensor (s :: ss) (ToCubicalTensor (TS xs)) = ToCubicalTensor $ TS $ 
  --   (\t => FromCubicalTensor ((takeTensor ss) (ToCubicalTensor t))) <$> takeFinVect' s xs

  namespace FullSlicing
    -- supporiting not just taking, but slicing
    -- i.e. t[2, :, 1, :] notation
    public export
    data MSliceT : (shape : List Nat) -> Type where
      Nil : MSliceT []
      (::) : Maybe (Fin (S m)) -> MSliceT ms -> MSliceT (m :: ms)

    ||| Computes the shape of the tensor after the slicing
    public export
    msliceToShape : {shape : List Nat} -> MSliceT shape -> List Nat
    msliceToShape [] = []
    msliceToShape {shape = (s :: _)} (Nothing :: sls) = s :: msliceToShape sls
    msliceToShape ((Just sl) :: sls) = finToNat sl :: msliceToShape sls
    
    -- sliceToShape Nil = []
    -- sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

    





{-
From this:
(\n => () !> (\_ => Fin n)) <$> shape
being equal to this:
[(() !> (\_ => Fin 2))] 

We should be able to infer that shape : Vect n Nat = [2]

We can simplify this to
f <$> shape
being equal to
[f 2]
where f : Nat -> Type

Can we from this, for an arbitrary f, infer that shape = [2]?
 -}