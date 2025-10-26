import sympy.Basic


@[main]
private lemma main
  {a b : ℕ} :
-- imply
  Int.subNatNat a b = (a - b : ℤ) := by
-- proof
  apply Int.subNatNat_eq_coe


-- created on 2025-03-28
-- updated on 2025-03-29
