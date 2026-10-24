import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
  (x y : K) (hxy : (W.map (algebraMap R K)).toAffine.Equation x y)
  (hψ : ((W.map (algebraMap R K)).preΨ n).eval x = 0) :
  -- imply
  x ∈ Set.range (algebraMap R K) ∧ y ∈ Set.range (algebraMap R K) := by
  -- proof
  classical
  have hn0 : ((n : ℕ) : R) ≠ 0 := hn.ne_zero
  have hψ' : Polynomial.aeval x (W.preΨ' n) = 0 := by
    have : ((W.map (algebraMap R K)).preΨ n) = (W.preΨ' n).map (algebraMap R K) := by
      rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.preΨ_ofNat]
    rw [this, Polynomial.eval_map, ← Polynomial.aeval_def] at hψ
    refine hψ
  have hlc : IsUnit (W.preΨ' n).leadingCoeff := by
    rw [W.leadingCoeff_preΨ' hn0]
    split_ifs with he
    ·
      obtain ⟨m, hm⟩ := he
      have hnm : n / 2 = m := by omega
      rw [hnm]
      have : ((n : ℕ) : R) = (m : R) * 2 := by
        rw [hm]
        push_cast
        ring
      rw [this] at hn
      refine isUnit_of_mul_isUnit_left hn
    · refine hn
  obtain ⟨u, hu⟩ := hlc
  have hmonic : (Polynomial.C (↑u⁻¹ : R) * W.preΨ' n).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hu, Units.inv_mul]
  have hxint : _root_.IsIntegral R x := by
    refine ⟨Polynomial.C (↑u⁻¹ : R) * W.preΨ' n, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hψ', mul_zero]
  obtain ⟨x₀, hx₀⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› hxint
  subst hx₀
  refine ⟨⟨x₀, rfl⟩, ?_⟩
  set b : R := W.a₁ * x₀ + W.a₃ with hb
  set c : R := -(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hc
  have heq : y ^ 2 + algebraMap R K b * y + algebraMap R K c = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff] at hxy
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hxy
    rw [hb, hc]
    simp only [map_add, map_mul, map_neg, map_pow]
    linear_combination hxy
  let Q : Polynomial R := Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C c)
  have hQmonic : Q.Monic := by
    apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2)
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le b) (by norm_num)
    · refine lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  have hyint : _root_.IsIntegral R y := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [Q, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← heq]
    ring
  refine (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› hyint


-- created on 2026-10-20
