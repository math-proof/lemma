import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (v : List.Vector α n.succ) :
-- imply
  v.head = v[0] := by
-- proof
  simp [GetElem.getElem]


@[main]
private lemma fin
  {n : ℕ}
-- given
  (v : List.Vector α n.succ) :
-- imply
  v.head = v.get 0 :=
-- proof
  main v


-- created on 2025-07-11
