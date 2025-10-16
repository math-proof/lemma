import Lemma.List.EqInsertIdx.of.Gt_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.Nat.GeSub_1.of.Gt
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length
import Lemma.List.DropAppend.eq.Drop_Sub_Length.of.Ge_Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Algebra.Ge_Min.of.Ge
import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.EqMin.of.Le
import Lemma.List.DropCons.eq.Drop_Sub_1.of.Gt_0
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Algebra.EqAdd_Sub.of.Gt
open List Algebra Nat


@[main]
private lemma main
-- given
  (h : i < j)
  (a : List α)
  (x : α) :
-- imply
  (a.insertIdx i x).drop j = a.drop (j - 1) := by
-- proof
  by_cases h_i : i ≤ a.length
  ·
    rw [InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length h_i (by rfl) (j := i)]
    simp
    rw [DropAppend.eq.Drop_Sub_Length.of.Ge_Length] <;>
      rw [LengthTake.eq.Min_Length]
    ·
      rw [EqMin.of.Le h_i]
      have h_ji : j - i > 0 := by simpa
      rw [DropCons.eq.Drop_Sub_1.of.Gt_0 h_ji]
      simp
      rw [Add_Sub.eq.SubAdd.of.Ge (by linarith)]
      rw [EqAdd_Sub.of.Gt h]
    ·
      apply Ge_Min.of.Ge ∘ Ge.of.Gt
      assumption
  ·
    simp at h_i
    rw [EqInsertIdx.of.Gt_Length h_i]
    repeat rw [Drop.eq.Nil.of.Ge_Length]
    ·
      apply GeSub_1.of.Gt
      linarith
    ·
      linarith


-- created on 2025-10-03
