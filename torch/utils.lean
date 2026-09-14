import sympy.tensor.tensor
import Lemma.Nat.NotLt.is.Ge
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.GtLengthInsertIdxEraseIdx.of.GtLength
import Lemma.List.EqEraseIdx.of.LeLength
open List Tensor Nat

def Tensor.keepdim (X : Tensor α (s.eraseIdx dim)) : Tensor α s :=
  if h : dim < s.length then
    cast
      (by simp [List.EqSetInsertIdxEraseIdx.of.GtLength h])
      ((X.unsqueeze dim).repeat ⟨dim, GtLengthInsertIdxEraseIdx.of.GtLength h 1⟩ s[dim])
  else
    cast (by rw [EqEraseIdx.of.LeLength (Ge.of.NotLt h)]) X
