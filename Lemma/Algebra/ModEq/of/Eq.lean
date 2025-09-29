import sympy.Basic


@[main]
private lemma main
  {a b : ℕ}
  (h : a = b)
  (d : ℕ) :
-- imply
  a ≡ b [MOD d] := by
-- proof
  rw [h]


-- created on 2025-03-15
