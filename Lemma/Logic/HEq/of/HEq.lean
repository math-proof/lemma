import sympy.Basic


@[main]
private lemma Symm
  {f : α}
  {g : β}
-- given
  (h : HEq g f) :
-- imply
  HEq f g :=
-- proof
  HEq.symm h


-- created on 2025-07-15
