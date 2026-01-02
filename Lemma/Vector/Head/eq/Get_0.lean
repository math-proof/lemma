import sympy.Basic


@[main, comm, fin, fin.comm]
private lemma main
  {n : ℕ}
-- given
  (v : List.Vector α n.succ) :
-- imply
  v.head = v[0] := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-11
