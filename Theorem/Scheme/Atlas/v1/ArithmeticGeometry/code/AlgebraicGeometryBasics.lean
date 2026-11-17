module

public import Mathlib
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.AlgebraicGeometryBasics

public section

open Cardinal Order
open Order


/--
[transcendence_basis_lift_cardinalMk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AlgebraicGeometryBasics.lean)
-/
public theorem transcendence_basis_lift_cardinalMk_eq
  [Field k]
  [Field L]
  [Algebra k L]
  {ι : Type u}
  {ι' : Type v}
  {x : ι → L}
  {y : ι' → L}
-- given
  (hx : IsTranscendenceBasis k x)
  (hy : IsTranscendenceBasis k y) :
-- imply
  Cardinal.lift.{v, u} (Cardinal.mk ι) = Cardinal.lift.{u, v} (Cardinal.mk ι') :=
-- proof
  hx.lift_cardinalMk_eq hy


-- created on 2026-10-23
