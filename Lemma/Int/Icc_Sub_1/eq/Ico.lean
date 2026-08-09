import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
-- given
  (a b : ℤ) :
-- imply
  Icc a (b - 1) = Ico a b := by
-- proof
  apply Set.ext
  simp [Set.mem_Icc, Set.mem_Ico]


-- created on 2026-08-08
