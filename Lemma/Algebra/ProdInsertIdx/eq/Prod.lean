import sympy.Basic


@[main]
private lemma main
  [MulOneClass α]
-- given
  (v : List α)
  (i : ℕ) :
-- imply
  (v.insertIdx i 1).prod = v.prod := by
-- proof
  induction v generalizing i <;>
    cases i <;>
      simp_all


-- created on 2025-06-08
