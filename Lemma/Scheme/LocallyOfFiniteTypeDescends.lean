import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean)
-/
@[path]
private lemma main :
-- imply
  DescendsAlong (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
-- proof
  refine HasRingHomProperty.descendsAlong (P := @LocallyOfFiniteType) (P' := @Surjective ⊓ @Flat)
    (Q := fun f => f.FiniteType) (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) RingHom.FiniteType.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩


-- created on 2026-10-20
