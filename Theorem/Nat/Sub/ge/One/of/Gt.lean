module

public import Theorem.Nat.LeAdd_1.of.Lt
public import Theorem.Nat.Add
public import Theorem.Nat.LeAddS.is.Le
public import Theorem.Nat.Le.of.Lt
public import Theorem.Nat.EqAddSub.of.Ge

public section

open Nat


public theorem Nat.Sub.ge.One.of.Gt
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b > a) :
-- imply
  b - a ≥ 1 := by
-- proof
  have h_ge := LeAdd_1.of.Lt h
  rw [Add.comm] at h_ge
  have h_le := Le.of.Lt h
  have h_eq := EqAddSub.of.Ge h_le
  rw [← h_eq] at h_ge
  apply Le.of.LeAddS h_ge


-- created on 2025-06-21
