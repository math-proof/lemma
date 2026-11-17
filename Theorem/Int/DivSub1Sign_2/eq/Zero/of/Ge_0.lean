module

public import Def.Data.List.Slice
public import Theorem.Nat.Gt.is.Ge.Ne
public import Theorem.Int.EqSign_1.of.Gt_0

public section

open Nat Int


public theorem Int.DivSub1Sign_2.eq.Zero.of.Ge_0
  {n : ℤ}
-- given
  (h : n ≥ 0) :
-- imply
  (1 - sign n) / 2 = 0 := by
-- proof
  if h_n : n = 0 then
    subst n
    simp
  else
    have h_n := Gt.of.Ge.Ne h h_n
    have := EqSign_1.of.Gt_0 h_n
    rw [this]
    simp


-- created on 2025-06-26
