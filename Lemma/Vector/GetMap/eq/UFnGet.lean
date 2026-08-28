import sympy.Basic


@[main, fin]
private lemma main
  {β : Type*}
-- given
  (v : List.Vector α n)
  (f : α → β)
  (i : Fin n) :
-- imply
  (v.map f)[i] = f (v[i]) := by
-- proof
  simp


-- created on 2024-07-01
