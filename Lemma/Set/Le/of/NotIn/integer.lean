import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n a : ℤ}
-- given
  (h : n ∉ Finset.Ico a (n + 1)) :
-- imply
  n ≤ a - 1 := by
-- proof
  by_contra h₁
  push Not at h₁
  apply h
  rw [Finset.mem_Ico]
  constructor <;> omega


-- created on 2021-06-06
