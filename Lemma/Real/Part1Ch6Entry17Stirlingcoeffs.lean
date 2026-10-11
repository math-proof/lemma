import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch6Entry17Stirlingcoeffs

/--
[Part1Ch6Entry17Stirlingcoeffs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry17Stirlingcoeffs.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry17_stirlingcoeffs_eq
-- given
  (a b m nu x : ℝ)
  (hx : |x| ≤ 1)
  (hnu : |nu| < 1)
  (hboundary : |x| = 1 → |m * nu| < 1)
  (hm : m ≠ 0)
  (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
-- imply
  (∀ k : ℕ, 1 - nu * x ^ k ≠ 0) ∧
    Summable (fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)) ∧
    Summable (fun k : ℕ => ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
      (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))) ∧
    Summable (fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2) ∧
    ∑' k : ℕ, (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k) =
      ∑' k : ℕ, ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
        (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k)) +
        b / m * ∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2 := by
-- proof
  apply Ramanujan.Part1Ch6.Entry17Stirlingcoeffs.ramanujan_part1_ch6_entry17_stirlingcoeffs a b m nu x hx hnu hboundary hm hmx

-- created on 2026-10-10
