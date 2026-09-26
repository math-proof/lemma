import Lemma.Real.Le_MulAddSum_ExpSum.of.Le.All_Ge_0.All_Ge_0.All_Le_AddMulAdd1.Ge_0
open Finset Real


@[main]
private lemma main
  {u b c : ℕ → ℝ}
  {n₀ n₁ n : ℕ}
-- given
  (h₀ : 0 ≤ u n₀)
  (h₁ : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (h₂ : ∀ n ≥ n₀, c n ≥ 0)
  (h₃ : ∀ n ≥ n₀, b n ≥ 0)
  (h₄ : n ∈ Ico n₀ n₁) :
-- imply
  u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
-- proof
  obtain ⟨hn₀, hn₁⟩ := mem_Ico.1 h₄
  have hb : ∑ k ∈ Ico n₀ n, b k ≤ ∑ k ∈ Ico n₀ n₁, b k :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hn₁.le) fun i hi _ => h₃ i (by grind)
  have hc : ∑ i ∈ Ico n₀ n, c i ≤ ∑ i ∈ Ico n₀ n₁, c i :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hn₁.le) fun i hi _ => h₂ i (by grind)
  calc
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) :=
      Le_MulAddSum_ExpSum.of.Le.All_Ge_0.All_Ge_0.All_Le_AddMulAdd1.Ge_0 h₀ h₁ h₂ h₃ hn₀
    _ ≤ _ := mul_le_mul (by linarith) (exp_le_exp.2 hc) (exp_pos _).le (by linarith [sum_nonneg fun i (hi : i ∈ Ico n₀ n₁) => h₃ i (by grind)])


-- created on 2026-09-26