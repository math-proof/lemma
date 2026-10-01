import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  p ∨ r ↔ q ∨ r :=
-- proof
  or_congr h Iff.rfl


-- created on 2022-01-27
