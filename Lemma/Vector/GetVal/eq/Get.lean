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


-- created on 2025-05-27
