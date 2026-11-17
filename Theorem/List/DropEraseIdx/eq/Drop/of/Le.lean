module

public import Theorem.List.EqEraseIdx.of.LeLength
public import Theorem.List.EraseIdx.eq.Append_Drop_Add_1
public import Theorem.List.DropAppend.eq.Drop.of.LeLength
public import Theorem.List.LengthTake.eq.Min_Length
public import Theorem.Nat.Ge_Min.of.Ge
public import Theorem.Nat.EqMin.of.Lt
public import Theorem.Nat.AddAdd
public import Theorem.Nat.EqAdd_Sub.of.Ge

public section

open List Nat


public theorem List.DropEraseIdx.eq.Drop.of.Le
-- given
  (h : i ≤ j)
  (s : List α) :
-- imply
  (s.eraseIdx i).drop j = s.drop (j + 1) := by
-- proof
  if h_i : i < s.length then
    rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [DropAppend.eq.Drop.of.LeLength] <;>
      rw [LengthTake.eq.Min_Length]
    ·
      rw [EqMin.of.Lt h_i]
      simp
      rw [AddAdd.comm]
      rw [EqAdd_Sub.of.Ge h]
    ·
      apply Ge_Min.of.Ge h
  else
    simp at h_i
    rw [EqEraseIdx.of.LeLength h_i]
    repeat rw [Drop.eq.Nil.of.LeLength (by linarith)]


-- created on 2025-10-03
