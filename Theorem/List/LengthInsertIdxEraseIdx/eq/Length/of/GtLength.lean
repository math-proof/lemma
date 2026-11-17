module

public import Theorem.List.LengthInsertIdx.eq.Add1Length.of.GeLength
public import Theorem.Nat.Le_Sub_1.of.Lt
public import Theorem.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
public import Theorem.Nat.EqAdd_Sub.of.Ge
public import Theorem.Nat.Ge_1.of.Gt

public section

open List Nat


public theorem List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength
  {d : ℕ}
  {s : List α}
-- given
  (h : s.length > d)
  (a : α) :
-- imply
  ((s.eraseIdx d).insertIdx d a).length = s.length := by
-- proof
  rw [LengthInsertIdx.eq.Add1Length.of.GeLength] <;>
    rw [LengthEraseIdx.eq.SubLength_1.of.GtLength h]
  ·
    apply (EqAdd_Sub.of.Ge ∘ Ge_1.of.Gt) h
  ·
    apply Le_Sub_1.of.Lt h


-- created on 2025-10-04
