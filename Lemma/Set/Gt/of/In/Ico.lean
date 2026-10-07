import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n b : ℤ}
-- given
  (h : b < n) :
-- imply
  n ∈ Set.Ici (b + 1) := by
-- proof
  rw [Set.mem_Ici]
  exact Int.add_one_le_iff.mpr h


-- created on 2021-04-14
