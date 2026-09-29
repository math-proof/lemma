import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ∨ q) :
-- imply
  p ∨ q ∨ r :=
-- proof
  h.elim Or.inl (fun hq => Or.inr (Or.inl hq))


-- created on 2026-09-27
