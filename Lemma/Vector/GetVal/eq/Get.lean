import sympy.Basic


@[main]
private lemma main
-- given
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  v.val[i] = v[i] :=
-- proof
  rfl


@[main]
private lemma fin
-- given
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  v.val.get ⟨i, by simp⟩ = v.get i :=
-- proof
  rfl


-- created on 2025-05-27
