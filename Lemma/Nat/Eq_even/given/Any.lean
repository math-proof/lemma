import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 = 0) :
-- imply
  ∃ k : ℤ, n = k * 2 := by
-- proof
  refine ⟨n / 2, ?_⟩
  omega


-- created on 2023-05-26
