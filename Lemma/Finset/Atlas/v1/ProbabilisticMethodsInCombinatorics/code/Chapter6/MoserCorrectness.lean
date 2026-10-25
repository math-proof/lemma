import Mathlib
import sympy.Basic
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness.Part3
open Finset MoserCorrectness


namespace MoserCorrectness

/--
[entropy_compression_arith](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean)
-/
@[path]
lemma entropy_compression_arith
  {n k : ℕ}
-- given
  (hk : k ≥ 3) :
-- imply
  n + (n + 2) * (k - 1) + 1 < k * (n + 2) := by
-- proof
  have hk_pos : 0 < k := by omega
  have hk_sub : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
  have key : (n + 2) * (k - 1) + (n + 2) = k * (n + 2) := by
    calc (n + 2) * (k - 1) + (n + 2)
      = (n + 2) * ((k - 1) + 1) := by ring
      _ = (n + 2) * k := by rw [hk_sub]
      _ = k * (n + 2) := by ring
  linarith

end MoserCorrectness

namespace MoserCorrectness

/--
[entropy_compression_pow_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean)
-/
@[path]
lemma entropy_compression_pow_bound
  {n k : ℕ}
-- given
  (hk : k ≥ 3) :
-- imply
  2 ^ n * 2 ^ ((n + 2) * (k - 1) + 1) < 2 ^ (k * (n + 2)) := by
-- proof
  rw [← Nat.pow_add]
  exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (entropy_compression_arith n k hk)

end MoserCorrectness

namespace MoserCorrectness

/--
[recover_prev_state](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean)
-/
@[path]
lemma recover_prev_state
  {n k : ℕ}
  {vars_seq : ℕ → Fin k → Fin n}
  {σ₀ : Fin n → Bool}
  {bits₁ bits₂ : ℕ → Fin k → Bool}
  {violating : ℕ → Fin k → Bool}
  {t : ℕ}
-- given
  (hviol₁ : ∀ t i, stepSt vars_seq σ₀ bits₁ t (vars_seq t i) = violating t i)
  (hviol₂ : ∀ t i, stepSt vars_seq σ₀ bits₂ t (vars_seq t i) = violating t i)
  (heq_next : stepSt vars_seq σ₀ bits₁ (t + 1) = stepSt vars_seq σ₀ bits₂ (t + 1)) :
-- imply
  stepSt vars_seq σ₀ bits₁ t = stepSt vars_seq σ₀ bits₂ t := by
-- proof
  funext v
  by_cases hv : ∃ i : Fin k, vars_seq t i = v
  · obtain ⟨i, hi⟩ := hv
    rw [← hi, hviol₁ t i, hviol₂ t i]
  · have h1 : stepSt vars_seq σ₀ bits₁ (t + 1) v = stepSt vars_seq σ₀ bits₁ t v := by
    simp only [stepSt, resampleFn, dif_neg hv]
    have h2 : stepSt vars_seq σ₀ bits₂ (t + 1) v = stepSt vars_seq σ₀ bits₂ t v := by
      simp only [stepSt, resampleFn, dif_neg hv]
    rw [← h1, ← h2, heq_next]

end MoserCorrectness


-- created on 2026-10-23
