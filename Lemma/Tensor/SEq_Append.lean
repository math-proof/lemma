import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.List.LengthSlice.eq.Min
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.NotLt.is.Ge
import Lemma.Nat.Lt_Min.is.Lt.Lt
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.Le.of.Lt_Add_1
import Lemma.Fin.Eq.of.Val
open Tensor List Bool Nat Fin


@[main]
private lemma main
  {n : ℕ}
-- given
  (X : Tensor α (n :: s))
  (i : Fin (n + 1)) :
-- imply
  X ≃ X[:i] ++ X[i:] := by
-- proof
  have h : (i : ℕ) ≤ n := Le.of.Lt_Add_1 i.isLt
  have h_Xn : X.length = n := by simp [Tensor.length]
  refine SEq.of.All_SEqGetS.Eq.Eq ?_ rfl ?_
  ·
    rw [h_Xn, LengthSlice.eq.Min, LengthSlice.eq.SubMin]
    omega
  ·
    intro t
    apply SEq.of.Eq
    have h_len0 : (⟨0, (i : ℕ), 1⟩ : Slice).length X.length = i := by
      rw [h_Xn, LengthSlice.eq.Min]
      simp [h]
    have h_len1 : (⟨(i : ℕ), X.length, 1⟩ : Slice).length X.length = n - i := by
      rw [h_Xn, LengthSlice.eq.SubMin]
      simp
    if h_t : (t : ℕ) < i then
      have h_lt : (t : ℕ) < (⟨0, (i : ℕ), 1⟩ : Slice).length X.length := by
        rwa [h_len0]
      erw [GetAppend.eq.Get.of.Lt h_lt]
      have h_min : (t : ℕ) < (i : ℕ) ⊓ n :=
        (Lt_Min.is.Lt.Lt (t : ℕ) (i : ℕ) n).mpr ⟨h_t, Nat.lt_of_lt_of_le h_t h⟩
      symm
      erw [GetGetSlice.eq.Get.of.Lt_Min (n := (i : ℕ)) X h_min]
      simp [GetElem.getElem]
    else
      have h_ge : (t : ℕ) ≥ (⟨0, (i : ℕ), 1⟩ : Slice).length X.length := by
        rw [h_len0]
        exact Ge.of.NotLt h_t
      have h_lt : (t : ℕ) < (⟨0, (i : ℕ), 1⟩ : Slice).length X.length + (⟨(i : ℕ), X.length, 1⟩ : Slice).length X.length := by
        rw [h_len0, h_len1]
        omega
      erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge h_ge h_lt]
      simp [h_len0]
      have h_k : (t : ℕ) - (i : ℕ) < X.length ⊓ n - i := by
        simp [h_Xn]
        omega
      have h_slice := GetGetSlice.eq.Get_Add.of.GtSubMin (m := n) (n := X.length) (j := (i : ℕ)) h_k X
      simp at h_slice
      erw [h_slice]
      simp [GetElem.getElem]
      congr 1
      apply Eq.of.Val
      simp
      exact (EqAdd_Sub.of.Ge (Ge.of.NotLt h_t)).symm


-- created on 2023-03-31
