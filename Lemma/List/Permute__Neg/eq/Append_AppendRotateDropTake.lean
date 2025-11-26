import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Cons.eq.Append
import Lemma.List.Cons_Append.eq.AppendCons
import Lemma.List.DropTake.eq.ListGet
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.Slice.eq.Nil
import Lemma.List.SliceTake.eq.Slice.of.Ge
import Lemma.List.Slice_0.eq.Take
import Lemma.List.TakeDrop.eq.Slice
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Gt
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.Ge_1
import Lemma.Nat.Gt_0
import Lemma.Nat.LeAdd_1
import Lemma.Nat.Sub.eq.Zero.of.Lt
import Lemma.Nat.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.SubAdd.eq.Sub_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  s.permute i (-d) = (s.take (i + 1)).take (i - d) ++ ((s.take (i + 1)).drop (i - d)).rotate (d ⊓ i) ++ s.drop (i + 1) := by
-- proof
  have h_i := LeAdd_1 i
  by_cases h_i' : i + 1 = s.length
  ·
    have h_i' := Eq_Mk.of.EqVal (Eq_Sub.of.EqAdd h_i')
    rw [h_i']
    rw [Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      simp [EqAddSub.of.Ge (Ge_1 i)]
    ·
      apply Gt_0 i
  ·
    unfold List.permute
    simp
    match h_d : (-d : ℤ) with
    | .ofNat d =>
      simp_all
      simp [Slice.eq.Nil]
      simp [Append_Append.eq.AppendAppend]
    | .negSucc d =>
      simp_all
      if h_d : d + 1 ≤ i then
        simp [h_d]
        rw [Rotate.eq.AppendDrop__Take.of.GeLength]
        ·
          simp
          rw [EqAddSub.of.Ge (by simp_all)]
          rw [Append_Append.eq.AppendAppend]
          rw [Cons.eq.Append]
          repeat rw [Append_Append.eq.AppendAppend]
          apply EqAppendS.of.Eq
          rw [TakeDrop.eq.Slice]
          rw [EqAddSub.of.Ge (by assumption)]
          rw [TakeTake.eq.Take.of.Ge (by simp_all; linarith)]
          repeat rw [AppendAppend.eq.Append_Append]
          apply EqAppendS.of.Eq.left
          rw [DropTake.eq.ListGet]
          apply EqAppendS.of.Eq.left
          rw [SliceTake.eq.Slice.of.Ge]
          linarith
        ·
          rw [LengthDrop.eq.SubLength]
          rw [LengthTake.eq.Min_Length]
          rw [EqMin.of.Le (by linarith)]
          rw [Sub_Sub.eq.SubAdd.of.Ge (by assumption)]
          rw [Add.comm (b := d + 1)]
          rw [SubAdd.eq.Add_Sub.of.Ge (by linarith)]
          linarith
      else
        simp at h_d
        have h_d := Sub.eq.Zero.of.Lt h_d
        rw [h_d]
        simp
        rw [Slice_0.eq.Take]
        rw [Cons_Append.eq.AppendCons]
        apply EqAppendS.of.Eq
        rw [EqMin.of.Gt (by assumption)]
        rw [Rotate.eq.AppendDrop__Take.of.GeLength]
        ·
          rw [TakeTake.eq.Take.of.Ge (by linarith)]
          rw [Cons.eq.Append]
          apply EqAppendS.of.Eq
          simp [DropTake.eq.ListGet]
        ·
          simp_all


@[main]
private lemma simp
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  s.permute i (-d) = s.take (i - d) ++ ((s.take (i + 1)).drop (i - d)).rotate (d ⊓ i) ++ s.drop (i + 1) := by
-- proof
  rw [main i d]
  rw [TakeTake.eq.Take.of.Ge (by simp_all; linarith)]


-- created on 2025-06-18
-- updated on 2025-10-27
