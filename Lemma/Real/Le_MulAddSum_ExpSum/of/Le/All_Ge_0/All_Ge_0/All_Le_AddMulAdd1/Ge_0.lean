import Mathlib.Analysis.SpecialFunctions.Exp
import Lemma.Real.Le_AddMulProd_SumMulProd.of.Le.All_Ge_0.All_Le_AddMulAdd1
open Finset Real


@[main]
private lemma main
  {u b c : ℕ → ℝ}
  {n₀ n : ℕ}
-- given
  (h₀ : 0 ≤ u n₀)
  (h₁ : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (h₂ : ∀ n ≥ n₀, c n ≥ 0)
  (h₃ : ∀ n ≥ n₀, b n ≥ 0)
  (h₄ : n₀ ≤ n) :
-- imply
  u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
-- proof
  have hP : ∀ a, n₀ ≤ a → ∏ i ∈ Ico a n, (1 + c i) ≤ exp (∑ i ∈ Ico n₀ n, c i) := fun a ha =>
    calc
      _ ≤ ∏ i ∈ Ico a n, exp (c i) :=
        prod_le_prod (fun i hi => by linarith [h₂ i (by grind)]) fun i _ => by linarith [add_one_le_exp (c i)]
      _ = exp (∑ i ∈ Ico a n, c i) := (exp_sum _ _).symm
      _ ≤ _ := exp_le_exp.2 (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left ha) fun i hi _ => h₂ i (by grind))
  calc
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) + ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
      Le_AddMulProd_SumMulProd.of.Le.All_Ge_0.All_Le_AddMulAdd1 h₁ h₂ h₄
    _ ≤ u n₀ * exp (∑ i ∈ Ico n₀ n, c i) + ∑ k ∈ Ico n₀ n, b k * exp (∑ i ∈ Ico n₀ n, c i) :=
      add_le_add (mul_le_mul_of_nonneg_left (hP n₀ le_rfl) h₀)
        (sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hP (k + 1) (by grind)) (h₃ k (by grind)))
    _ = _ := by
      rw [← sum_mul]
      ring


-- created on 2026-09-26