module

public import Instance.Data.Tensor.Tensor.Part2
public import Theorem.Nat.NotLt.is.Ge
public import Theorem.List.EqSetInsertIdxEraseIdx.of.GtLength
public import Theorem.List.GtLengthInsertIdxEraseIdx.of.GtLength
public import Theorem.List.EqEraseIdx.of.LeLength

@[expose] public section

open List Tensor Nat


def Tensor.keepdim (X : Tensor α (s.eraseIdx dim)) : Tensor α s :=
  if h : dim < s.length then
    cast
      (by simp [List.EqSetInsertIdxEraseIdx.of.GtLength h])
      ((X.unsqueeze dim).repeat ⟨dim, GtLengthInsertIdxEraseIdx.of.GtLength h 1⟩ s[dim])
  else
    cast (by rw [EqEraseIdx.of.LeLength (Ge.of.NotLt h)]) X

