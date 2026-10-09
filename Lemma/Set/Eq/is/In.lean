import sympy.Basic


@[path]
private lemma main
  {f : α → α}
  {x : α} :
-- imply
  f x = x ↔ x ∈ {x | f x = x} :=
-- proof
  Iff.rfl


-- created on 2019-09-13
