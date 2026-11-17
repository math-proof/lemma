module
public import Mathlib

public section


public theorem Nat.Eq_Sub_1.of.Val.eq.Sub_1
  {i : Fin n}
-- given
  (h : i.val = n - 1) :
-- imply
  i = ⟨n - 1, by linarith [i.isLt]⟩ := by
-- proof
  aesop


-- created on 2025-06-17
