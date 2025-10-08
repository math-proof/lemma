import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≤ y) :
-- imply
  x.toNat ≤ y.toNat := by
-- proof
  obtain hx | hx := le_total 0 x <;>
    obtain hy | hy := le_total 0 y <;>
      simp_all
  linarith

-- created on 2025-05-28
