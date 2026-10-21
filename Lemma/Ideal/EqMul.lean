import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit.lean)
-/
@[path]
private lemma main
    {L : Type*} [Field L] (A : ValuationSubring L) (I : Ideal ↥A) (hI : I ≠ ⊤)
    (hsep : ∀ x : ↥A, (∀ n : ℕ, x ∈ I ^ n) → x = 0)
    (α β : ↥A) (u : (AdicCompletion I ↥A)ˣ)
    (h : algebraMap (↥A) (AdicCompletion I ↥A) α = algebraMap (↥A) (AdicCompletion I ↥A) β * u) :
    ∃ v : (↥A)ˣ, α = β * v := by
  classical
  have hIm : I ≤ IsLocalRing.maximalIdeal ↥A := IsLocalRing.le_maximalIdeal hI
  have hred : ∀ n : ℕ, 0 < n → ∃ w : ↥A, IsUnit w ∧ α - β * w ∈ I ^ n := by
    intro n hn
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n (u : AdicCompletion I ↥A))
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n (↑u⁻¹ : AdicCompletion I ↥A))
    have hwy : Ideal.Quotient.mk (I ^ n) (w * y) = 1 := by
      rw [map_mul, hw, hy, ← map_mul, Units.mul_inv, map_one]
    have hIn : I ^ n ≤ IsLocalRing.maximalIdeal ↥A := (Ideal.pow_le_self hn.ne').trans hIm
    have hwunit : IsUnit w := by
      have h1 : w * y - 1 ∈ I ^ n := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hwy, map_one, sub_self]
      have h2 : w * y - 1 ∈ IsLocalRing.maximalIdeal ↥A := hIn h1
      have h3 : IsUnit (w * y) := by
        by_contra hnu
        have hmem : w * y ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
          have := Ideal.sub_mem _ hmem h2
          rwa [sub_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
      exact isUnit_of_mul_isUnit_left h3
    refine ⟨w, hwunit, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, ← AdicCompletion.evalₐ_of, ← AdicCompletion.evalₐ_of,
      ← map_mul, ← map_sub]
    have hof : ∀ x : ↥A, AdicCompletion.of I (↥A) x = algebraMap (↥A) (AdicCompletion I ↥A) x := fun x => rfl
    rw [hof, hof, h, sub_self, map_zero]
  rcases ValuationRing.dvd_total β α with ⟨t, ht⟩ | ⟨t, ht⟩
  ·
    by_cases htu : IsUnit t
    · exact ⟨htu.unit, by rw [IsUnit.unit_spec]; exact ht⟩
    ·
      have htm : t ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr htu
      have hβ : β = 0 := by
        apply hsep
        intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        obtain ⟨w, hw, hmem⟩ := hred n hn
        have htw : IsUnit (t - w) := by
          by_contra hnu
          have h1 : t - w ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
          have h2 : w ∈ IsLocalRing.maximalIdeal ↥A := by
            have := Ideal.sub_mem _ htm h1
            rwa [sub_sub_cancel] at this
          exact (IsLocalRing.mem_maximalIdeal _).mp h2 hw
        have hprod : β * (t - w) ∈ I ^ n := by
          have : α - β * w = β * (t - w) := by rw [ht]; ring
          rwa [this] at hmem
        have := Ideal.mul_mem_right (↑htw.unit⁻¹ : ↥A) _ hprod
        rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
      refine ⟨1, ?_⟩
      rw [Units.val_one, mul_one, ht, hβ, zero_mul]
  ·
    by_cases htu : IsUnit t
    · refine ⟨htu.unit⁻¹, ?_⟩
      rw [ht, mul_assoc, IsUnit.mul_val_inv, mul_one]
    · have htm : t ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr htu
      have hα : α = 0 := by
        apply hsep
        intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        obtain ⟨w, hw, hmem⟩ := hred n hn
        have htw : IsUnit (1 - t * w) := by
          by_contra hnu
          have h1 : 1 - t * w ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
          have h2 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
            have := Ideal.add_mem _ h1 (Ideal.mul_mem_right w _ htm)
            rwa [sub_add_cancel] at this
          exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one)
        have hprod : α * (1 - t * w) ∈ I ^ n := by
          have : α - β * w = α * (1 - t * w) := by rw [ht]; ring
          rwa [this] at hmem
        have := Ideal.mul_mem_right (↑htw.unit⁻¹ : ↥A) _ hprod
        rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
      refine ⟨1, ?_⟩
      rw [Units.val_one, mul_one, hα]
      rw [ht, hα, zero_mul]

-- created on 2026-10-20
