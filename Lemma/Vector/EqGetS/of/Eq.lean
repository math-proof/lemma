import sympy.Basic


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a = b)
  (i : Fin n):
-- imply
  a[i] = b[i] := by
-- proof
  rw [h]


@[main]
private lemma fin
  {a b : List.Vector α n}
-- given
  (h : a = b)
  (i : Fin n):
-- imply
  a.get i = b.get i := by
-- proof
  rw [h]


-- created on 2025-09-23
