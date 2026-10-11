import sympy.Basic


@[path]
private lemma main
  {s₀ B : Finset α}
-- given
  (h : s₀.card = B.card) :
-- imply
  s₀.card = B.card := by
-- proof
  apply h


-- created on 2026-10-11
