module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Nat.Sub.gt.Zero.is.Gt
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  tsub_pos_iff_lt



public theorem Nat.Gt.of.Sub.gt.Zero
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} (h : b - a > 0) : b > a :=
  (Nat.Sub.gt.Zero.is.Gt).mp h

public theorem Nat.Sub.gt.Zero.of.Gt
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} (h : b > a) : b - a > 0 :=
  (Nat.Sub.gt.Zero.is.Gt).mpr h

-- created on 2025-10-16
