module Data.Container.Morphism

import Data.Container.Definition

||| Dependent lenses
||| Forward-backward container morphisms
public export
record (=%>) (c1, c2 : Cont) where
  constructor (<!)
  fwd : c1.shp -> c2.shp
  bwd : (x : c1.shp) -> c2.pos (fwd x) -> c1.pos x

export infixr 1 =%>
export infix 1 <!

||| Dependent charts
||| Forward-forward container morphisms
public export
record (=&>) (c1, c2 : Cont) where
  constructor (<&!)
  fwd : c1.shp -> c2.shp
  fwd' : (x : c1.shp) -> c1.pos x -> c2.pos (fwd x)

export infixr 1 =&>
export infix 1 <&!

val : Cont -> Type -> Cont
val (shp !> pos) r = (!>) shp (\s => pos s -> r)

-- Chart -> DLens morphism 
-- Tangent bundle to Contanget bundle, effectively
valContMap : {c1, c2 : Cont} -> {r : Type}
  ->  (f : c1 =&> c2)
  ->  (c1 `val` r) =%> (c2 `val` r)
valContMap {c1=(shp !> pos)} {c2=(shp' !> pos')} (fwd <&! fwd')
  = fwd <! (\x, k, x' => k (fwd' x x'))


-- ||| A container morphism
-- public export
-- record (~%>) (c1, c2 : ContF R) where
--   constructor (<~!)
--   fwd' : c1.shp' -> c2.shp'


-- upd : c1 ~%> c2 -> 
-- %pair (=%>) fwd bwd



-- Composition of container morphisms
-- public export
-- (⨾) : a =%> b -> b =%> c -> a =%> c
-- (⨾) x y =
--     (y.fwd . x.fwd) <!
--     (\z => x.bwd z . y.bwd (x.fwd z))

-- export infixl 5 ⨾