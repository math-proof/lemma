module

public import Theorem.Nat.Le_Sub.is.LeAdd.of.Le
public import Theorem.Nat.Sub.eq.Zero.of.Lt

public section

open Nat


public theorem Nat.LtSub.of.Lt
  {j n : ℕ}
-- given
  (h : j < n)
  (i : ℕ):
-- imply
  j - i < n := by
-- proof
  if h_le : j ≥ i then
    by_contra h
    simp at h
    have := Ge_Add.of.GeSub.Le h_le h
    linarith
  else
    simp at h_le
    have h := Sub.eq.Zero.of.Lt h_le
    rw [h]
    linarith


-- created on 2025-06-21
