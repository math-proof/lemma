module

public import Mathlib

public section


public theorem Nat.Ne_0.of.Lt0Mul.left
  [PartialOrder α] [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


public theorem Nat.Ne_0.of.Lt0Mul
  [PartialOrder α] [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  b ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


-- created on 2024-11-30
-- updated on 2026-10-26
