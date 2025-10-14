import sympy.Basic


@[main, comm]
private lemma main
  [Semiring α]
  -- given
  (d : ℕ) :
-- imply
  OfNat.ofNat (α := α) d = Nat.cast d :=
-- proof
  Lean.Grind.Semiring.ofNat_eq_natCast d


-- created on 2025-06-17
