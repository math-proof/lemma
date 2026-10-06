import Mathlib
import sympy.Basic


/--
[IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R] [Field k] [Field K]
  {π : R →+* k}
  {φ : R →+* K}
-- given
  (hπ : Function.Surjective π) :
-- imply
  ∃ ρ : φ.range →+* k, ∀ r : R, ρ (φ.rangeRestrict r) = π r := by
-- proof
  have hker : RingHom.ker φ ≤ RingHom.ker π := by
    have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  refine ⟨φ.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨π, ?_⟩, fun r => ?_⟩
  · intro x hx
    apply hker
    rw [RingHom.mem_ker] at hx ⊢
    have := congrArg Subtype.val hx
    simpa using this
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r


-- created on 2026-10-05
