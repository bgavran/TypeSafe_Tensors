module Data.Container.Definition

import Data.Fin
import Data.Vect

import Data.Tree
import Data.Functor.Naperian
import Misc

%hide Data.Vect.fromList
%hide Builtin.fst

-- Inspired by Andre's code: https://gitlab.com/avidela/types-laboratory/-/tree/main/src/Data/Container?ref_type=heads

||| A container is a pair: a shape and a set of positions indexed by that shape
||| They can be used to describe various data types
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  shp : Type
  ||| For each shape, a position
  pos : shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

public export
Const2 : Type -> Type -> Cont
Const2 x y = (_ : x) !> y

public export
Const : Type -> Cont
Const x = Const2 x x

public export
CUnit : Cont
CUnit = Const Unit

||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.shp
  indexCont : c.pos shapeExt -> x

||| Container c can be said to be "full off" a type x
||| Sometimes used as infix operator to aid readability
||| c `fullOf` x is easier to read than Ext c x
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

public export
EmptyExt : Ext (Const2 () l) ()
EmptyExt = () <| \_ => ()

public export
liftA2ConstCont : Ext (Const2 () l) a -> Ext (Const2 () l) b -> Ext (Const2 () l) (a, b)
liftA2ConstCont (() <| va) (() <| vb) = () <| (\x => (va x, vb x))

||| The extension of any container with a unit shape
||| is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
public export
Applicative (Ext (Const2 () l)) where
  pure a = () <| (\_ => a)
  fs <*> xs = uncurry ($) <$> liftA2ConstCont fs xs 

||| The extension of any container with a unit shape
||| is an Naperian functor
public export
{l : Type} -> Naperian (Ext (Const2 () l)) where
  Log = l
  lookup = indexCont
  tabulate t = () <| t


public export infixr 0 ><
||| Hancock, Dirichlet, or tensor product of containers
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
(shp !> pos) >< (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')

public export infixr 0 >+<
||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
(shp !> pos) >+< (shp' !> pos') = (es : Either shp shp') !> (case es of
  Left s => pos s
  Right s' => pos' s')


public export infixr 0 >@<
||| Composition of containers (polynomial composition)
||| Non-symmetric in general
||| Monoid with CUnit
public export
(>@<) : Cont -> Cont -> Cont
c >@< d = ((sh <| ind) : Ext c (d.shp)) !> (cp : c.pos sh ** d.pos (ind cp))



||| Specialised to Hancock tensor product
||| Could be as simple as foldr (><) CUnit, but want to take care of associativity
public export
prodConts : List Cont -> Cont
prodConts = foldr (><) CUnit
-- prodConts [] = CUnit
-- prodConts (c :: cs) = c >< prodConts cs

