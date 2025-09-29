import sympy.Basic


@[main]
private lemma main
  {x : List α}
-- given
  (h_i : i < x.length)
  (h : d ≠ i)
  (a : α) :
-- imply
  have : i < (x.set d a).length := by simpa
  (x.set d a)[i] = x[i] := by
-- proof
  simp_all


-- created on 2025-07-05
-- updated on 2025-07-17
