import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  a ⊓ b = a := by
-- proof
  simp [h]


-- created on 2025-05-07
