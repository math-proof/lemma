module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.CoeMul.eq.MulCoeS
  [NonAssocSemiring α]
  {a b : ℕ} :
-- imply
  ((a * b : ℕ) : α) = a * b :=
-- proof
  Nat.cast_mul a b


-- created on 2025-03-30
-- updated on 2026-10-26
