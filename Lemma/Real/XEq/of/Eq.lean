import sympy.sets.fancyset
import sympy.Basic


@[main]
private lemma main
  [XEq α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a ≈ b := by
-- proof
  subst h
  rfl


-- created on 2026-01-02
