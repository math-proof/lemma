import sympy.Basic


@[main]
private lemma main
  {x : List α}
-- given
  (h_i : i < x.length)
  (a : α) :
-- imply
  have : i < (x.set i a).length := by simpa
  (x.set i a)[i] = a := by
-- proof
  simp


-- created on 2025-07-18
