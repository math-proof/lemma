import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (z : ℤ)
  (n : ℕ) :
-- imply
  z.toNat ≤ n ↔ z ≤ n :=
-- proof
  Int.toNat_le


-- created on 2025-05-24
