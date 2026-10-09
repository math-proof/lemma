import sympy.Basic


@[path, comm]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Int.ofNat d = Nat.cast d :=
-- proof
  Int.ofNat_eq_natCast d


-- created on 2025-10-14
