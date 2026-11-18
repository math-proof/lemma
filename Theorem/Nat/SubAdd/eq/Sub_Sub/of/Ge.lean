module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.EqSubAdd
public import Theorem.Nat.Sub_Add.eq.SubSub

public section

open Nat


@[comm]
public theorem Nat.SubAdd.eq.Sub_Sub.of.Ge
  {b c : ℕ}
-- given
  (h : b ≥ c)
  (a : ℕ) :
-- imply
  a + c - b = a - (b - c) := by
-- proof
  let d := b - c
  have h_b : b = d + c := by
    simp [d, h]
  rw [h_b]
  rw [EqSubAdd]
  rw [Add.comm (a := d)]
  rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd]


public theorem Nat.Sub_Sub.eq.SubAdd.of.Ge
  {b c : ℕ}
  (h : b ≥ c)
  (a : ℕ) :
  a - (b - c) = a + c - b :=
  (Nat.SubAdd.eq.Sub_Sub.of.Ge h a).symm


-- created on 2025-06-20
