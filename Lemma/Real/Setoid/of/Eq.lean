import sympy.Basic


@[main]
private lemma main
  [Setoid α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a ≈ b := by
-- proof
  subst h
  rfl


-- created on 2026-01-02
