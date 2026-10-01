import sympy.Basic


@[main]
private lemma main
  {f : α → α}
  {x : α} :
-- imply
  f x = x ↔ x ∈ {x | f x = x} :=
-- proof
  Iff.rfl


-- created on 2026-09-27
