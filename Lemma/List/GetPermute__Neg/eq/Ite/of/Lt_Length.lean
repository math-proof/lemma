import Lemma.List.Permute.eq.Ite
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.Nat.EqMin.of.Lt
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.Slice.eq.Nil
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.GetSlice.eq.Get_Add.of.Lt_LengthSlice
import Lemma.Nat.LeSub.is.Le_Add
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Nat.Sub.ge.One.of.Gt
import Lemma.Nat.LtSub
open List Nat


@[main]
private lemma main
  {a : List α}
  {i : Fin a.length}
  {d t : ℕ}
-- given
  (h : t < a.length) :
-- imply
  have : t < (a.permute i (-d)).length := by simpa
  (a.permute i (-d))[t] =
    if t < i - d then
      a[t]
    else if t = i - d then
      a[i]
    else if t ≤ i then
      a[t - 1]
    else
      a[t] := by
-- proof
  have h_sub := LtSub i d
  simp [Permute.eq.Ite]
  split_ifs with h_d
  ·
    have h_t : t < (a.take (i - d)).length + (a[(i : ℕ)] :: (a.slice (i - d) i ++ a.drop (i + 1))).length := by
      rw [LengthCons.eq.Add1Length]
      rw [LengthAppend.eq.AddLengthS]
      rw [LengthSlice.eq.SubMin]
      grind
    apply Eq.symm
    split_ifs with h_i h_eq h_1
    ·
      grind
    ·
      grind
    ·
      simp at h_i
      have h_i := LeSub.of.Le_Add h_i
      have h_i' := Lt.of.Le.Ne h_i (by simp_all [Ne.symm])
      have h_i'' := Sub.ge.One.of.Gt h_i'
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
      simp [EqMin.of.Lt h_sub]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by linarith)]
      rw [GetAppend.eq.Get.of.Lt_Length]
      rw [GetSlice.eq.Get_Add.of.Lt_LengthSlice]
      ·
        grind
      ·
        rw [LengthSlice.eq.SubMin]
        grind
    ·
      simp at h_i h_1 h_eq
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
      ·
        have h_i := LeSub.of.Le_Add h_i
        have h_i' := Lt.of.Le.Ne h_i (by simp_all [Ne.symm])
        have h_i'' := Sub.ge.One.of.Gt h_i'
        simp [EqMin.of.Lt h_sub]
        rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
        ·
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength] <;>
          ·
            simp [LengthSlice.eq.SubMin]
            grind
        ·
          linarith
      ·
        simp_all
  ·
    simp at h_d
    subst h_d
    simp [Slice.eq.Nil]
    grind


-- created on 2025-06-21
-- updated on 2025-10-25
