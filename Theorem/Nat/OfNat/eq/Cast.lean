module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.OfNat.eq.Cast
  [Semiring α]
  -- given
  (d : ℕ) :
-- imply
  OfNat.ofNat (α := α) d = Nat.cast d :=
-- proof
  Lean.Grind.Semiring.ofNat_eq_natCast d


-- created on 2025-06-17
