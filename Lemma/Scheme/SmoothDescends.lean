import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma desc_smooth_descendsAlong :
  DescendsAlong (@Smooth : MorphismProperty (Scheme : Type (u + 1)))
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong (P := @Smooth) (P' := @Surjective ⊓ @Flat)
    (Q := fun f => f.Smooth) (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) RingHom.Smooth.codescendsAlong_faithfullyFlat
  ·
    rw [inf_comm]
    apply inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  ·
    intro R S f hf
    apply (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩
/--
[AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean)
-/
@[path]
private lemma main :
  -- imply
  DescendsAlong (@Smooth : MorphismProperty (Scheme : Type (u + 1)))
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  -- proof
  apply desc_smooth_descendsAlong


-- created on 2026-10-20
