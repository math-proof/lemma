import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.DropAppend.eq.Drop.of.Ge_Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.Ge_Min.of.Ge
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.AddAdd
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i ≤ j)
  (a : List α) :
-- imply
  (a.eraseIdx i).drop j = a.drop (j + 1) := by
-- proof
  by_cases h_i : i < a.length
  ·
    rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [DropAppend.eq.Drop.of.Ge_Length] <;>
      rw [LengthTake.eq.Min_Length]
    ·
      rw [EqMin.of.Lt h_i]
      simp
      rw [AddAdd.comm]
      rw [EqAdd_Sub.of.Ge h]
    ·
      apply Ge_Min.of.Ge h
  ·
    simp at h_i
    rw [EqEraseIdx.of.Ge_Length h_i]
    repeat rw [Drop.eq.Nil.of.Ge_Length (by linarith)]


-- created on 2025-10-03
