import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.PolyReciprocalFrechetBound
open MvPolynomial DifferentialOperators


namespace DifferentialOperators

/--
[mvPolynomial_eval_norm_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PolyReciprocalFrechetBound.lean)
-/
@[path]
lemma mvPolynomial_eval_norm_le_pow
  {n : ℕ}
  {Q : MvPolynomial (Fin n) ℝ} :
-- imply
  ∃ A : ℝ, A > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), ‖MvPolynomial.eval (fun i => ξ i) Q‖ ≤ A * (1 + ‖ξ‖) ^ Q.totalDegree := by
-- proof
  open MvPolynomial Finset in
  set A := max 1 (Q.support.sum fun d => ‖Q.coeff d‖) with hA_def
  refine ⟨A, lt_of_lt_of_le one_pos (le_max_left _ _), fun ξ => ?_⟩
  rw [eval_eq (fun i => ξ i) Q]
  have h1ξ : 1 ≤ 1 + ‖ξ‖ := le_add_of_nonneg_right (norm_nonneg _)
  have h0ξ : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by positivity
  calc ‖∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, ξ i ^ d i‖
    ≤ Q.support.sum fun d => ‖Q.coeff d * ∏ i ∈ d.support, ξ i ^ d i‖ :=
      norm_sum_le _ _
    _ ≤ Q.support.sum fun d => ‖Q.coeff d‖ * (1 + ‖ξ‖) ^ Q.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      have hmon : ‖∏ i ∈ d.support, ξ i ^ d i‖ ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
        calc ‖∏ i ∈ d.support, ξ i ^ d i‖
          ≤ ∏ i ∈ d.support, ‖ξ i ^ d i‖ := norm_prod_le _ _
          _ = ∏ i ∈ d.support, ‖ξ i‖ ^ d i := by
            apply Finset.prod_congr rfl; intro i _; exact norm_pow _ _
          _ ≤ ∏ i ∈ d.support, ‖ξ‖ ^ d i := by
            apply Finset.prod_le_prod
            · intro i _; positivity
            · intro i _; exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ξ i) _
          _ = ‖ξ‖ ^ (d.support.sum fun i => d i) := by rw [Finset.prod_pow_eq_pow_sum]
          _ ≤ (1 + ‖ξ‖) ^ (d.support.sum fun i => d i) := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
            apply pow_le_pow_right₀ h1ξ
            have : (d.support.sum fun i => d i) = d.sum fun _ k => k := by
              simp [Finsupp.sum]
            rw [this]
            exact le_totalDegree hd
      calc ‖Q.coeff d * ∏ i ∈ d.support, ξ i ^ d i‖
        ≤ ‖Q.coeff d‖ * ‖∏ i ∈ d.support, ξ i ^ d i‖ := norm_mul_le _ _
        _ ≤ ‖Q.coeff d‖ * (1 + ‖ξ‖) ^ Q.totalDegree := by
          exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
    _ = (Q.support.sum fun d => ‖Q.coeff d‖) * (1 + ‖ξ‖) ^ Q.totalDegree := by
      rw [Finset.sum_mul]
    _ ≤ A * (1 + ‖ξ‖) ^ Q.totalDegree := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) h0ξ

end DifferentialOperators

namespace DifferentialOperators

/--
[mvPolynomial_evalAtReal_norm_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PolyReciprocalFrechetBound.lean)
-/
@[path]
lemma mvPolynomial_evalAtReal_norm_le_pow
  {n : ℕ}
  {Q : MvPolynomial (Fin n) ℂ} :
-- imply
  ∃ A : ℝ, A > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), ‖evalAtReal Q ξ‖ ≤ A * (1 + ‖ξ‖) ^ Q.totalDegree := by
-- proof
  open MvPolynomial Finset in
  set A := max 1 (Q.support.sum fun d => ‖Q.coeff d‖) with hA_def
  refine ⟨A, lt_of_lt_of_le one_pos (le_max_left _ _), fun ξ => ?_⟩
  unfold evalAtReal
  rw [eval_eq (fun i => (ξ i : ℂ)) Q]
  have h1ξ : 1 ≤ 1 + ‖ξ‖ := le_add_of_nonneg_right (norm_nonneg _)
  have h0ξ : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by positivity
  calc ‖∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖
    ≤ Q.support.sum fun d => ‖Q.coeff d * ∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖ :=
      norm_sum_le _ _
    _ ≤ Q.support.sum fun d => ‖Q.coeff d‖ * (1 + ‖ξ‖) ^ Q.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      have hmon : ‖∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖ ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
        calc ‖∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖
          ≤ ∏ i ∈ d.support, ‖(ξ i : ℂ) ^ d i‖ := norm_prod_le _ _
          _ = ∏ i ∈ d.support, ‖(ξ i : ℂ)‖ ^ d i := by
            apply Finset.prod_congr rfl; intro i _; exact norm_pow _ _
          _ = ∏ i ∈ d.support, ‖ξ i‖ ^ d i := by
            apply Finset.prod_congr rfl; intro i _
            congr 1; exact Complex.norm_real _
          _ ≤ ∏ i ∈ d.support, ‖ξ‖ ^ d i := by
            apply Finset.prod_le_prod
            · intro i _; positivity
            · intro i _; exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ξ i) _
          _ = ‖ξ‖ ^ (d.support.sum fun i => d i) := by rw [Finset.prod_pow_eq_pow_sum]
          _ ≤ (1 + ‖ξ‖) ^ (d.support.sum fun i => d i) := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
            apply pow_le_pow_right₀ h1ξ
            have : (d.support.sum fun i => d i) = d.sum fun _ k => k := by
              simp [Finsupp.sum]
            rw [this]
            exact le_totalDegree hd
      calc ‖Q.coeff d * ∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖
        ≤ ‖Q.coeff d‖ * ‖∏ i ∈ d.support, (ξ i : ℂ) ^ d i‖ := norm_mul_le _ _
        _ ≤ ‖Q.coeff d‖ * (1 + ‖ξ‖) ^ Q.totalDegree := by
          exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
    _ = (Q.support.sum fun d => ‖Q.coeff d‖) * (1 + ‖ξ‖) ^ Q.totalDegree := by
      rw [Finset.sum_mul]
    _ ≤ A * (1 + ‖ξ‖) ^ Q.totalDegree := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) h0ξ

end DifferentialOperators

namespace DifferentialOperators

/--
[reciprocal_poly_deriv_bound_multiIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PolyReciprocalFrechetBound.lean)
-/
@[path]
lemma reciprocal_poly_deriv_bound_multiIndex
  {n : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {m : ℕ}
  {C : ℝ}
  {js : List (Fin n)}
-- given
  (hm : 1 ≤ m)
  (hdeg : P.totalDegree ≤ m)
  (hP : HasPolyLowerBound P m C) :
-- imply
  ∃ Cα : ℝ, Cα > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), ‖ξ‖ > 1 / C → ‖iteratedPartialDeriv js (polyReciprocal P) ξ‖ ≤ Cα * ‖ξ‖ ^ (-(↑(m + js.length) : ℤ)) := by
-- proof
  set k := js.length
  obtain ⟨hC, hP_bound⟩ := hP
  obtain ⟨L, hLdeg, hL_eq⟩ := reciprocal_poly_structural P m hm hdeg js
  obtain ⟨A, hA_pos, hA_bound⟩ := mvPolynomial_evalAtReal_norm_le_pow L
  refine ⟨A * (1 + C) ^ ((m - 1) * k) / C ^ (1 + k), ?_, ?_⟩
  · exact div_pos (mul_pos hA_pos (pow_pos (by linarith) _)) (pow_pos hC _)
  · intro ξ hξ
    have hξ_pos : ‖ξ‖ > 0 := by linarith [div_pos one_pos hC]
    have hPξ_ne : evalAtReal P ξ ≠ 0 := by
      intro h
      have h1 := hP_bound ξ hξ
      simp only [h, norm_zero] at h1
      linarith [mul_pos hC (pow_pos hξ_pos m)]
    have hPξ_norm_pos : 0 < ‖evalAtReal P ξ‖ := by
      have := hP_bound ξ hξ
      linarith [mul_pos hC (pow_pos hξ_pos m)]
    have heq := hL_eq ξ hPξ_ne
    rw [heq]
    rw [norm_div, norm_pow]
    have hL_norm_bound : ‖evalAtReal L ξ‖ ≤ A * (1 + ‖ξ‖) ^ L.totalDegree :=
      hA_bound ξ
    have h_one_xi : 1 + ‖ξ‖ ≤ (1 + C) * ‖ξ‖ := by
      have : 1 < C * ‖ξ‖ := by
        rw [show (1 : ℝ) = C * (1 / C) from by field_simp]
        exact mul_lt_mul_of_pos_left hξ hC
      nlinarith
    have hPξ_lower := hP_bound ξ hξ
    have hPξ_pow_pos : 0 < ‖evalAtReal P ξ‖ ^ (1 + k) := pow_pos hPξ_norm_pos _
    have hD_pos : 0 < (C * ‖ξ‖ ^ m) ^ (1 + k) := by positivity
    calc ‖evalAtReal L ξ‖ / ‖evalAtReal P ξ‖ ^ (1 + k)
      ≤ A * (1 + ‖ξ‖) ^ L.totalDegree / ‖evalAtReal P ξ‖ ^ (1 + k) :=
        div_le_div_of_nonneg_right hL_norm_bound (by positivity)
      _ ≤ A * (1 + ‖ξ‖) ^ ((m - 1) * k) / ‖evalAtReal P ξ‖ ^ (1 + k) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hA_pos)
        apply pow_le_pow_right₀ (by linarith : 1 ≤ 1 + ‖ξ‖)
        exact le_trans hLdeg (Nat.le_refl _)
      _ ≤ A * ((1 + C) * ‖ξ‖) ^ ((m - 1) * k) / (C * ‖ξ‖ ^ m) ^ (1 + k) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + ‖ξ‖) h_one_xi _)
            (le_of_lt hA_pos))
          hD_pos
          (pow_le_pow_left₀ (by positivity) hPξ_lower _)
      _ = A * (1 + C) ^ ((m - 1) * k) / C ^ (1 + k) *
        ‖ξ‖ ^ (-(↑(m + k) : ℤ)) := by
        rw [mul_pow, mul_pow, zpow_neg, zpow_natCast, ← pow_mul]
        have hmk : m * (1 + k) = (m - 1) * k + (m + k) := by
          obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
          simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]; ring
        rw [hmk, pow_add]
        field_simp [pow_ne_zero _ (ne_of_gt hξ_pos), pow_ne_zero _ (ne_of_gt hC)]
        ring
end DifferentialOperators



-- created on 2026-10-23
