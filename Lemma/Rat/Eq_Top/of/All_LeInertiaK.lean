import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped NumberField


/-- ported from external source -/
@[path]
private lemma main
  [Field K] [NumberField K] [IsGalois ℚ K]
  {H : Subgroup (K ≃ₐ[ℚ] K)}
-- given
  (hH : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) :
-- imply
  H = ⊤ := by
  classical
    let F : IntermediateField ℚ K := FixedPoints.intermediateField H
    have hHF : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
    have hunr : ∀ (p : Ideal (𝓞 F)) [p.IsMaximal], Algebra.IsUnramifiedAt ℤ p := by
-- proof
      intro p hp
      have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField F)
      obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p
        (by
          rw [(RingHom.injective_iff_ker_eq_bot _).mp
            (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
          exact bot_le)
      have : P.LiesOver p := ⟨hPp.symm⟩
      have : (p.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ p
      have : P.LiesOver (p.under ℤ) := Ideal.LiesOver.trans P p (p.under ℤ)
      have h𝔭0 : p.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hp0
      have : Finite (ℤ ⧸ p.under ℤ) := Ring.HasFiniteQuotients.finiteQuotient h𝔭0
      have : Finite (𝓞 F ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp0
      have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K) (p.under ℤ) P
      have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := H) p P
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p.under ℤ) P (K ≃ₐ[ℚ] K),
        ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p.under ℤ) (q := P) h𝔭0] at c1
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P H,
        ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp0] at c2
      have c3 : Nat.card (P.inertia H) = Nat.card (P.inertia (K ≃ₐ[ℚ] K)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hH P hPmax)).toEquiv
      have hne : p.ramificationIdx' P ≠ 0 :=
        Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
      have he : (p.under ℤ).ramificationIdx' p = 1 := by
        have h : (p.under ℤ).ramificationIdx' P = p.ramificationIdx' P := by
          rw [← c1, ← c2, c3]
        rw [Ideal.ramificationIdx_algebra_tower' (p.under ℤ) p P] at h
        exact (mul_eq_right₀ hne).mp h
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr
        ((Ideal.ramificationIdx'_eq_ramificationIdx (p.under ℤ) p h𝔭0).symm.trans he)
    have hF : Module.finrank ℚ F = 1 := by
      by_contra hne
      obtain ⟨p, hpmax, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne
      exact hram (@hunr p hpmax)
    rw [← Subgroup.card_eq_iff_eq_top, IsGaloisGroup.card_eq_finrank H F K,
      IsGaloisGroup.card_eq_finrank (K ≃ₐ[ℚ] K) ℚ K, ← Module.finrank_mul_finrank ℚ F K, hF, one_mul]


-- created on 2026-10-23
