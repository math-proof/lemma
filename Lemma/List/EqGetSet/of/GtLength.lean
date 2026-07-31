import sympy.Basic


@[main]
private lemma main
  {x : List α}
-- given
  (h_i : x.length > i)
  (a : α) :
-- imply
  (x.set i a)[i]'(by simpa) = a := by
-- proof
  simp


-- created on 2025-07-18
