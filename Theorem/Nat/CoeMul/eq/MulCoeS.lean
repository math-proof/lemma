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


public theorem Nat.MulCoeS.eq.CoeMul
  [NonAssocSemiring α]
  {a b : ℕ} :
  (a * b : α) = ((a * b : ℕ) : α) :=
  (Nat.CoeMul.eq.MulCoeS (a := a) (b := b)).symm

-- created on 2025-03-30
-- updated on 2026-10-26
