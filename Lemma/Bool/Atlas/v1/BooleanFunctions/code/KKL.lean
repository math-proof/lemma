import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Talagrand
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
open Finset BigOperators Real


namespace BooleanFourier

/--
[expect_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma expect_sq_eq_one
  {n : ℕ}
  {f : BoolFn n}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1) :
-- imply
  expect (fun x => f x ^ 2) = 1 := by
-- proof
  simp only [expect]
  have h_sq : ∀ x, f x ^ 2 = 1 := by
    intro x
    obtain h | h <;> simp [h] := hf x
  simp_rw [h_sq]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool]

end BooleanFourier

namespace BooleanFourier

/--
[fourierInfluence_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma fourierInfluence_nonneg
  {n : ℕ}
  {f : BoolFn n}
  {i : Fin n} :
-- imply
  fourierInfluence f i ≥ 0 := by
-- proof
  simp only [fourierInfluence]
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> positivity

end BooleanFourier

namespace BooleanFourier

/--
[variance_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma variance_le_one
  {n : ℕ}
  {f : BoolFn n}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1) :
-- imply
  variance f ≤ 1 := by
-- proof
  have h1 : expect (fun x => f x ^ 2) = 1 := expect_sq_eq_one f hf
  simp only [variance, h1]
  linarith [sq_nonneg (expect f)]

end BooleanFourier

namespace BooleanFourier

/--
[log_le_two_mul_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma log_le_two_mul_sqrt
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  Real.log n ≤ 2 * Real.sqrt n := by
-- proof
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h := Real.log_le_self hsqrt_nonneg
  rw [Real.log_sqrt hn.le] at h
  linarith

end BooleanFourier

namespace BooleanFourier

/--
[kkl_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma kkl_theorem
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ), n ≥ 2 → ∀ (f : BoolFn n), (∀ x, f x = 1 ∨ f x = -1) → ∃ i : Fin n, fourierInfluence f i ≥ c * variance f * Real.log n / (n : ℝ) := by
-- proof
  obtain ⟨c₀, hc₀_pos, htal⟩ := talagrand_influence_inequality
  refine ⟨min (c₀ / 2) (1 / 2), by positivity, fun n hn f hf => ?_⟩
  set c := min (c₀ / 2) (1 / 2)
  have hn_pos : (n : ℝ) > 0 := by positivity
  have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
  have hlog_pos : Real.log (n : ℝ) > 0 := Real.log_pos hn_cast
  have hvar_le : variance f ≤ 1 := variance_le_one f hf
  have hc_pos : c > 0 := by positivity
  have hc_le_half : c ≤ 1 / 2 := min_le_right _ _
  have hc_le_c0_half : c ≤ c₀ / 2 := min_le_left _ _
  by_cases hvar : variance f ≤ 0
  ·
    refine ⟨⟨0, by omega⟩, ?_⟩
    have h_rhs : c * variance f * Real.log ↑n / (↑n : ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hc_pos.le hvar) hlog_pos.le
      · exact hn_pos.le
    linarith [fourierInfluence_nonneg f ⟨0, by omega⟩]
  ·
    push Not at hvar
    have htal_f := htal n f hf
    by_cases h_exists_big : ∃ i : Fin n, fourierInfluence f i ≥ 1 / Real.sqrt n
    ·
      obtain ⟨i, hi⟩ := h_exists_big
      refine ⟨i, le_trans ?_ hi⟩
      have h_sqrt_pos : Real.sqrt (n : ℝ) > 0 := Real.sqrt_pos.mpr hn_pos
      rw [div_le_div_iff₀ hn_pos h_sqrt_pos]
      rw [one_mul]
      have h_log_bound : Real.log (n : ℝ) ≤ 2 * Real.sqrt n := log_le_two_mul_sqrt hn_pos
      have h_sqrt_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hn_pos.le
      calc c * variance f * Real.log ↑n * Real.sqrt ↑n
        ≤ (1 / 2) * 1 * (2 * Real.sqrt ↑n) * Real.sqrt ↑n := by
          gcongr
        _ = Real.sqrt ↑n * Real.sqrt ↑n := by ring
        _ = ↑n := h_sqrt_sq
    ·
      push Not at h_exists_big
      have h_total_bound : c₀ / 2 * variance f * Real.log ↑n ≤ ∑ i : Fin n, fourierInfluence f i := by
        suffices h_key : (∑ i : Fin n, fourierInfluence f i / (1 + Real.log (1 / fourierInfluence f i)))
          * Real.log ↑n ≤ 2 * ∑ i : Fin n, fourierInfluence f i by
          have h2 : c₀ * variance f * Real.log ↑n ≤ 2 * ∑ i : Fin n, fourierInfluence f i := by
            calc c₀ * variance f * Real.log ↑n
              ≤ (∑ i : Fin n, fourierInfluence f i / (1 + Real.log (1 / fourierInfluence f i))) *
                Real.log ↑n := by
                exact mul_le_mul_of_nonneg_right htal_f hlog_pos.le
              _ ≤ 2 * ∑ i : Fin n, fourierInfluence f i := h_key
          linarith
        calc (∑ i : Fin n, fourierInfluence f i / (1 + Real.log (1 / fourierInfluence f i))) *
          Real.log ↑n
          = ∑ i : Fin n, fourierInfluence f i / (1 + Real.log (1 / fourierInfluence f i)) *
            Real.log ↑n := by rw [Finset.sum_mul]
          _ ≤ ∑ i : Fin n, 2 * fourierInfluence f i := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi_zero : fourierInfluence f i = 0
            · simp [hi_zero]
            ·
              have hi_pos : fourierInfluence f i > 0 :=
                lt_of_le_of_ne (fourierInfluence_nonneg f i) (Ne.symm hi_zero)
              have hi_bound := h_exists_big i
              have h_inv_bound : Real.sqrt ↑n < 1 / fourierInfluence f i := by
                have h_sqrt_pos : (0 : ℝ) < Real.sqrt ↑n := Real.sqrt_pos.mpr hn_pos
                have h1 : Real.sqrt ↑n * fourierInfluence f i < 1 := by
                  have h2 : Real.sqrt ↑n * (1 / Real.sqrt ↑n) = 1 := by
                    rw [mul_one_div_cancel]; exact h_sqrt_pos.ne'
                  nlinarith [mul_lt_mul_of_pos_left hi_bound h_sqrt_pos]
                rw [lt_div_iff₀' hi_pos]
                linarith
              have h_log_inv : Real.log (n : ℝ) / 2 < Real.log (1 / fourierInfluence f i) := by
                rw [← Real.log_sqrt hn_pos.le]
                exact Real.log_lt_log (Real.sqrt_pos.mpr hn_pos) h_inv_bound
              have h_denom_bound : Real.log (↑n : ℝ) / 2 < 1 + Real.log (1 / fourierInfluence f i) := by
                linarith
              have h_denom_pos : (0 : ℝ) < 1 + Real.log (1 / fourierInfluence f i) := by
                linarith [hlog_pos]
              rw [div_mul_eq_mul_div, div_le_iff₀ h_denom_pos]
              nlinarith [h_denom_bound]
          _ = 2 * ∑ i : Fin n, fourierInfluence f i := by rw [← Finset.mul_sum]
      have h_univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
        exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
      have h_const_sum : ∑ _i : Fin n, (c₀ / 2 * variance f * Real.log ↑n / ↑n) =
        c₀ / 2 * variance f * Real.log ↑n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      have h_pigeonhole : ∃ i ∈ (Finset.univ : Finset (Fin n)),
        c₀ / 2 * variance f * Real.log ↑n / ↑n ≤ fourierInfluence f i := by
        apply Finset.exists_le_of_sum_le h_univ_nonempty
        rwa [h_const_sum]
      obtain ⟨i, _, hi⟩ := h_pigeonhole
      refine ⟨i, le_trans ?_ hi⟩
      apply div_le_div_of_nonneg_right _ hn_pos.le
      apply mul_le_mul_of_nonneg_right _ hlog_pos.le
      exact mul_le_mul_of_nonneg_right hc_le_c0_half hvar.le

end BooleanFourier

namespace BooleanFourier

/--
[variance_balanced_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma variance_balanced_eq_one
  {n : ℕ}
  {f : BoolFn n}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1)
  (hbal : expect f = 0) :
-- imply
  variance f = 1 := by
-- proof
  simp only [variance, expect_sq_eq_one f hf, hbal]
  norm_num

end BooleanFourier

namespace BooleanFourier

/--
[kkl_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/KKL.lean)
-/
@[path]
lemma kkl_balanced
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ), n ≥ 2 → ∀ (f : BoolFn n), (∀ x, f x = 1 ∨ f x = -1) → expect f = 0 → ∃ i : Fin n, fourierInfluence f i ≥ c * Real.log n / (n : ℝ) := by
-- proof
  obtain ⟨c, hc_pos, hkkl⟩ := kkl_theorem
  refine ⟨c, hc_pos, fun n hn f hf hbal => ?_⟩
  obtain ⟨i, hi⟩ := hkkl n hn f hf
  refine ⟨i, ?_⟩
  have hvar : variance f = 1 := variance_balanced_eq_one f hf hbal
  rw [hvar] at hi
  simp only [mul_one] at hi
  linarith

end BooleanFourier


-- created on 2026-10-23
