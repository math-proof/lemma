module

public import Theorem.List.Cons_Append.eq.AppendCons
public import Theorem.List.DropTake.eq.ListGet
public import Theorem.List.LengthTake.eq.Min_Length
public import Theorem.List.Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0
public import Theorem.List.SliceTake.eq.Slice.of.Ge
public import Theorem.List.TakeDrop.eq.Slice
public import Theorem.Nat.EqSub.of.EqAdd
public import Theorem.Fin.Eq_Fin.of.EqVal
public import Theorem.Nat.Ge_1
public import Theorem.Nat.Gt_0
public import Theorem.Nat.LeAdd_1
public import Theorem.Nat.NotLe.is.Gt
public import Theorem.Nat.SubAdd.eq.Add_Sub.of.Ge
public import Theorem.Nat.SubAdd.eq.Sub_Sub.of.Ge

public section

open List Nat Fin Set


public theorem List.Permute__Neg.eq.Append_AppendRotateDropTake
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
    have h_i' := Eq_Fin.of.EqVal (Eq_Sub.of.EqAdd h_i')
    rw [h_i']
    rw [Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      simp [EqAddSub.of.Ge (Ge_1 i)]
    ·
      grind
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
          apply Append.of.Eq
          rw [TakeDrop.eq.Slice]
          rw [EqAddSub.of.Ge (by assumption)]
          rw [TakeTake.eq.Take.of.Ge (by simp_all; linarith)]
          repeat rw [AppendAppend.eq.Append_Append]
          apply Append.of.Eq.left
          rw [DropTake.eq.ListGet]
          apply Append.of.Eq.left
          rw [SliceTake.eq.Slice.of.Ge]
          linarith
        ·
          rw [LengthDrop.eq.SubLength]
          rw [LengthTake.eq.Min_Length]
          rw [EqMin.of.Le (by linarith [i.isLt])]
          rw [Sub_Sub.eq.SubAdd.of.Ge (by assumption)]
          rw [Add.comm (b := d + 1)]
          rw [SubAdd.eq.Add_Sub.of.Ge (by linarith)]
          linarith
      else
        have h_d := Nat.Gt.of.NotLe h_d
        simp [Sub.eq.Zero.of.Lt h_d]
        rw [Slice_0.eq.Take]
        rw [Cons_Append.eq.AppendCons]
        apply Append.of.Eq
        rw [EqMin.of.Gt (by omega)]
        rw [Rotate.eq.AppendDrop__Take.of.GeLength]
        ·
          rw [TakeTake.eq.Take.of.Ge (by linarith)]
          rw [Cons.eq.Append]
          apply Append.of.Eq
          simp [DropTake.eq.ListGet]
        ·
          simp_all


public theorem simp
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
