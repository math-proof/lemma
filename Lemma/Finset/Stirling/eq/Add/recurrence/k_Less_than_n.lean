import sympy.functions.combinatorial.numbers
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
-- given
  (_h₀ : 1 ≤ k)
  (_h₁ : k < n) :
-- imply
  Stirling (n + 1) (k + 1) = Stirling n k + (k + 1) * Stirling n (k + 1) := by
-- proof
  unfold Stirling
  rw [Nat.stirlingSecond_succ_succ, add_comm]


-- created on 2020-10-06
