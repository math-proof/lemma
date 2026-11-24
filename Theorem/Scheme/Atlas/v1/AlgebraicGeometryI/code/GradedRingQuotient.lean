module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingQuotient.Part2
open Polynomial GradedRingQuotient


public section

/--
[monomial_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingQuotient.lean)
-/
@[path]
private theorem monomial_mem_reesAlgebra_eq
  {A : Type u}
  [CommRing A]
  {I : Ideal A}
  {p : ℕ}
  {a : A}
-- given
  (ha : a ∈ I ^ p) :
-- imply
  Polynomial.monomial p a ∈ reesAlgebra I := by
-- proof
  apply GradedRingQuotient.monomial_mem_reesAlgebra I p a ha


-- created on 2026-10-23
