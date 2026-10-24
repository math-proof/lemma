import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AlgebraicGeometryBasics
open Cardinal Order
open Order


/--
[transcendence_basis_lift_cardinalMk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AlgebraicGeometryBasics.lean)
-/
@[path]
lemma transcendence_basis_lift_cardinalMk_eq
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
