module

public import Theorem.Nat.EqMin.of.Le
public import Theorem.Nat.LeAddS.is.Le
public import Theorem.Nat.EqMin.of.Gt
public import Theorem.Nat.LtAddS.is.Lt

public section

open Nat


public theorem Nat.MinAddS.eq.AddMin
  [LinearOrder α]
  [Add α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
-- given
  (a b c: α) :
-- imply
  (a + c) ⊓ (b + c) = a ⊓ b + c := by
-- proof
  if h : a ≤ b then
    rw [EqMin.of.Le h]
    have h' := LeAddS.of.Le (a := c) h
    rw [EqMin.of.Le h']
  else
    simp at h
    rw [EqMin.of.Gt h]
    have h' := GtAddS.of.Gt (a := c) h
    rw [EqMin.of.Gt h']


-- created on 2025-06-18
