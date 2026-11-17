module

public import Theorem.Nat.Gt_0
public import Theorem.Nat.Gt_0.of.Ne_0

public section

open Nat


public theorem Nat.GtVal_0.of.Ne_0
  {n : Fin m}
-- given
  (h : n ≠ ⟨0, Gt_0 n⟩) :
-- imply
  n.val > 0 := by
-- proof
  suffices n.val ≠ 0 by
    exact Gt_0.of.Ne_0 this
  intro hval
  apply h
  ext
  assumption


-- created on 2025-10-05
