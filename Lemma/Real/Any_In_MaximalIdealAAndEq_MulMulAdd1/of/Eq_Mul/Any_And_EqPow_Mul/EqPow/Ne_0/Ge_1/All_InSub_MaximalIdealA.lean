import Mathlib
import sympy.Basic


/--
[IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {n : ℕ}
  {c : A}
  {π : A}
  {ϖt : A}
  {αt : A}
-- given
  (σ : A ≃+* A)
  (hσ : ∀ a : A, σ a - a ∈ IsLocalRing.maximalIdeal A)
  (hn : 1 ≤ n)
  (hc : c ≠ 0)
  (hπ : π ^ n = c)
  (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ n = c * u)
  (hα : σ π = αt * π) :
-- imply
  ∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ σ ϖt = αt * ϖt * (1 + m) := by
-- proof
  have hn0 : n ≠ 0 := by omega
  obtain ⟨u, hu, hϖtn⟩ := hϖt

  have key : ∃ w : A, IsUnit w ∧ ϖt = π * w := by
    obtain ⟨d, hd⟩ := ValuationRing.cond π ϖt
    rcases hd with hd | hd
    · refine ⟨d, ?_, hd.symm⟩
      have h1 : c * u = c * d ^ n := by rw [← hϖtn, ← hd, mul_pow, hπ]
      have h2 : u = d ^ n := mul_left_cancel₀ hc h1
      exact (isUnit_pow_iff hn0).mp (h2 ▸ hu)
    · have h1 : c * 1 = c * (u * d ^ n) := by
        rw [mul_one, ← mul_assoc, ← hϖtn, ← mul_pow, hd, hπ]
      have h2 : (1 : A) = u * d ^ n := mul_left_cancel₀ hc h1
      have hdn : IsUnit (d ^ n) := IsUnit.of_mul_eq_one u (by rw [mul_comm]; exact h2.symm)
      have hdu : IsUnit d := (isUnit_pow_iff hn0).mp hdn
      obtain ⟨dU, rfl⟩ := hdu
      refine ⟨↑dU⁻¹, Units.isUnit _, ?_⟩
      rw [← hd, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨w, hw, hϖw⟩ := key
  obtain ⟨wU, rfl⟩ := hw
  refine ⟨(σ ↑wU - ↑wU) * ↑wU⁻¹, Ideal.mul_mem_right _ _ (hσ _), ?_⟩
  have h1 : (1 : A) + (σ ↑wU - ↑wU) * ↑wU⁻¹ = σ ↑wU * ↑wU⁻¹ := by
    rw [sub_mul, Units.mul_inv]; ring
  rw [h1, hϖw, map_mul, hα]
  have e : αt * (π * ↑wU) * (σ ↑wU * ↑wU⁻¹) = αt * π * σ ↑wU * (↑wU * ↑wU⁻¹) := by ring
  rw [e, Units.mul_inv, mul_one]


-- created on 2026-10-05
