import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Append_DropTake.eq.Take
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.TailRotate.eq.Take.of.EqLength_Add_1
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
open List Nat


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d) :
-- imply
  (s.permute i (-d)).eraseIdx (i - d) = s.eraseIdx i := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateDropTake]
  rw [EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length (by simp; omega)]
  rw [EqMin.of.Le (by omega)]
  rw [TakeTake.eq.Take.of.Ge (by omega)]
  rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simp)]
  simp
  rw [EqMin.of.Le (by omega)]
  simp
  rw [TailRotate.eq.Take.of.EqLength_Add_1]
  ·
    rw [DropTake.eq.TakeDrop]
    rw [TakeTake.eq.Take.of.Ge (by omega)]
    rw [TakeDrop.eq.DropTake]
    rw [EqAddSub.of.Ge h]
    rw [Append_Append.eq.AppendAppend]
    rw [Append_DropTake.eq.Take]
    grind
  ·
    simp
    omega


-- created on 2025-10-31
