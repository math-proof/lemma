import sympy.Basic


@[main, comm]
private lemma main
-- given
  (v : List α) :
-- imply
  v.eraseIdx 0 = v.drop 1 := by
-- proof
  simp


-- created on 2025-09-23
