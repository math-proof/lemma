module

public import Theorem.Nat.Mul
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm]
public theorem Nat.MulMul.eq.Mul_Mul
  [Semigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (b * c) :=
-- proof
  mul_assoc a b c


@[comm]
public theorem Nat.MulMul.eq.Mul_Mul.comm
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (c * b) := by
-- proof
  grind


@[comm]
public theorem swap
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = b * (a * c) := by
-- proof
  grind


@[comm]
public theorem rotate
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = b * (c * a) := by
-- proof
  grind


@[comm]
public theorem permute
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = c * (a * b) := by
-- proof
  grind


@[comm]
public theorem reverse
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = c * (b * a) := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-08-02
