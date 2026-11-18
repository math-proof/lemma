module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Nat.CoeSub.eq.SubCoeS.of.Ge
public import Theorem.Nat.Ge.of.Gt

public section

open Nat


@[comm]
public theorem Nat.CoeSub.eq.SubCoeS.of.Gt
  [AddGroupWithOne Z]
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  ((a - b : ℕ) : Z) = a - b := by
-- proof
  apply CoeSub.eq.SubCoeS.of.Ge
  apply Ge.of.Gt h



public theorem Nat.SubCoeS.eq.CoeSub.of.Gt
  [AddGroupWithOne Z]
  {a b : ℕ}
  (h : a > b) :
  (a : Z) - b = ((a - b : ℕ) : Z) :=
  (Nat.CoeSub.eq.SubCoeS.of.Gt h).symm

-- created on 2025-05-04
