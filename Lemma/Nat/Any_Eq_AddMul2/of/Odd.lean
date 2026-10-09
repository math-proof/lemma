import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {n : ℤ}
  -- given
  (h : n % 2 = 1)
  -- imply
  : ∃ k : ℤ, n = 2 * k + 1 := by
  -- proof
  have hdiv : n = n % 2 + 2 * (n / 2) := by linarith [Int.emod_add_mul_ediv n 2]
  refine ⟨n / 2, ?_⟩
  linarith

-- created on 2018-05-28
