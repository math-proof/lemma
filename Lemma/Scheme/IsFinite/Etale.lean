import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isFinite_of_isOpenImmersion_of_isClosed_range
  {V U : (Scheme : Type (u + 1))} (i : V ⟶ U) [IsOpenImmersion i]
  (hi : IsClosed (Set.range i.base)) :
  IsFinite i := by
  have : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i hi
  infer_instance
/--
[AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range.lean)
-/
@[path]
private lemma main
  {V U X : (Scheme : Type (u + 1))} (i : V ⟶ U) [IsOpenImmersion i] (hi : IsClosed (Set.range i.base))
  (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π] :
  IsFinite (i ≫ π) ∧ AlgebraicGeometry.Etale (i ≫ π) := by
  have : IsFinite i := isFinite_of_isOpenImmersion_of_isClosed_range i hi
  refine ⟨inferInstance, inferInstance⟩


-- created on 2026-10-20
