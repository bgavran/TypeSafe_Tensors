module Data.Container.Applicative

import Data.Fin

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.Morphism
import Misc

%hide Builtin.infixr.(#)

||| Applicative Container
||| Consists of a container and a proof that its extension is an applicative functor
public export
record ApplC where
  constructor (#)
  GetC : Cont
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

%pair ApplC GetC applPrf

||| Every natural number n corresponds to a Vect n, which is applicative
||| Used in cubical tensors whose shapes are defined by lists of natural numbers
public export
NatToVect : (n : Nat) -> ApplC
NatToVect n = # (Vect n)

public export
NatsToVect : (shape : List Nat) -> ApplC
NatsToVect shape = NatToVect (prod shape)

||| Specialised to composition product of containers
public export
ComposeContainers : List ApplC -> Cont
ComposeContainers cs = foldr (>@<) CUnit (GetC <$> cs)


||| Data type for ergonomic construction of lists of applicative containers
||| Allows us to construct a list of applicative containers using the usual list syntax, while leaving the proof of applicativity *implicit*
||| Idris's auto search automatically takes care of that
public export
data ApplContList : List ApplC -> Type where
  Nil : ApplContList []
  (::) : (c : Cont) ->
    Applicative (Ext c) =>
    (cs : ApplContList cs') -> ApplContList ((# c) :: cs')

||| TODO can be removed, likely just like the above stuff was possible to remove, by operating directly on conts : List ApplC
||| Used to convert a cubical tensor's shape to an applicative container list
public export
NatsToApplConts : (shape : List Nat) -> ApplContList (NatToVect <$> shape)
NatsToApplConts [] = []
NatsToApplConts (s :: ss) = Vect s :: NatsToApplConts ss

public export
FlatStorage : (shape : List Nat) -> ApplContList [NatsToVect shape]
FlatStorage shape = [Vect (prod shape)]


||| Given a list of natural numbers, when we convert this to composition product of containers, this will have a unit shape
||| We don't do rewrites to prove this (as it's not definitionally equal to unit shape, but only isomorphic)
||| Hence, just like with EmptyExt we provide convenience functions to create this unit shape easily
public export
emptyShapeCubicalTensor : {shape : List Nat} ->
  (ComposeContainers (NatToVect <$> shape)) .shp
emptyShapeCubicalTensor {shape = []} = ()
emptyShapeCubicalTensor {shape = (_ :: _)}
  = () <| (\_ => emptyShapeCubicalTensor)


public export
natsToFinProd : (shape : List Nat) -> Type
natsToFinProd shape = Fin (prod shape)

public export
CubicalTensorCont : (shape : List Nat) -> Cont
CubicalTensorCont shape = (_ : Unit) !> (natsToFinProd shape)

public export
cubicalTensorToFlat : {shape : List Nat} ->
  ComposeContainers [NatsToVect shape] =%> 
  CubicalTensorCont shape
cubicalTensorToFlat {shape = []} = constUnit <%! (\(() <| _), _ => (FZ ** ()))
cubicalTensorToFlat {shape = (s :: ss)}
  = constUnit <%! (\(() <| _), ieva => (ieva ** ()))
  

public export
flatToCubicalTensor : {shape : List Nat} ->
  CubicalTensorCont shape =%> 
  ComposeContainers [NatsToVect shape]
flatToCubicalTensor {shape = []} = (\_ => EmptyExt) <%! (\_, _ => FZ)
flatToCubicalTensor {shape = (s :: ss)}
  = (\_ => EmptyExt) <%! (\(), (cp ** ()) => cp)

-- public export
-- cubicalTensorProdNat : {shape : List Nat} ->
--   ComposeContainers (NatToVect <$> shape) =%> 
--   CubicalTensorCont shape
-- cubicalTensorProdNat {shape = []} = constUnit <%! const2Unit
-- cubicalTensorProdNat {shape = (_ :: _)}
--   = constUnit <%! (\(() <| ind), (fs, rst) =>
--     (fs ** let (_ <%! bw) = cubicalTensorProdNat
--            in bw (ind fs) rst))


||| TODO should go through a flat representation?
public export
reshapeMap : {oldShape, newShape : List Nat} ->
  {auto prf : prod oldShape = prod newShape} ->
  (natsToFinProd oldShape -> natsToFinProd newShape)
reshapeMap {oldShape} {newShape} x = ?reshapeMap_rhs

public export
dLensProductReshape : {oldShape, newShape : List Nat} ->
  {auto prf : prod oldShape = prod newShape} ->
  CubicalTensorCont oldShape =%> CubicalTensorCont newShape
dLensProductReshape {prf}
  = constUnit <%! (\_ => rewrite prf in id)


-- public export
-- prodNatToCubicalTensor : {shape : List Nat} ->
--   CubicalTensorCont shape =%> 
--   ComposeContainers (NatToVect <$> shape)
-- prodNatToCubicalTensor {shape = []} = constUnit <%! const2Unit
-- prodNatToCubicalTensor {shape = (s :: ss)}
--   = let (fwss <%! bwss) = prodNatToCubicalTensor {shape=ss}
--     in (\_ => () <| \_ => fwss ()) <%! (\(), (cp ** rst) => (cp, bwss () rst))



-- shapeOfCubicalTensorIsUnit : {shape : List Nat} ->
--   (ComposeContainers (NatToVect <$> shape)) .shp = ()
-- shapeOfCubicalTensorIsUnit {shape = []} = Refl
-- shapeOfCubicalTensorIsUnit {shape = (s :: ss)}
--   = rewrite shapeOfCubicalTensorIsUnit {shape = ss} in ?afasdf

-- public export
-- ComposeContainers' : {conts : List ApplC} ->
--   ApplContList conts -> ApplC
-- ComposeContainers' [] = # CUnit
-- ComposeContainers' (c :: cs) =
--   (#) (c >< prodConts (applContListToContList cs))
--     {applPrf = ?ComposeContainers_rhs_1}
