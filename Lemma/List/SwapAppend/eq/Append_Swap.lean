import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.GetSwap.eq.Ite.of.GtLength.GtLength.GtLength
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.Nat.EqSubAdd
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.Nat.LtSub.is.Lt_Add.of.Ge
import Lemma.Nat.Ne_Sub.of.NeAdd.Ge
import Lemma.List.GetSwap.eq.Get.of.Lt_LengthSwap.GtLength
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.List.EqSwap.of.Ge_Length
open List Bool Nat


@[main]
private lemma main
-- given
  (a b : List α)
  (i j : ℕ) :
-- imply
  (a ++ b).swap (a.length + i) (a.length + j) = a ++ b.swap i j := by
-- proof
  if h : i < b.length ∧ j < b.length then
    ext k x
    if h : k < a.length + b.length then
      let h' := h
      rw [← LengthSwap.eq.Length b i j] at h
      rw [AddLengthS.eq.LengthAppend] at h
      let h'' := h'
      rw [AddLengthS.eq.LengthAppend] at h'
      rw [← LengthSwap.eq.Length (a ++ b) (a.length + i) (a.length + j)] at h'
      simp_all
      apply IffEqS.of.Eq
      rw [GetSwap.eq.Ite.of.GtLength.GtLength.GtLength (by simp_all) (by simp_all) (by simp_all)]
      repeat rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by linarith) (by simp_all)]
      if h_k : k < a.length then
        repeat rw [GetAppend.eq.Get.of.GtLength (by simp_all)]
        split_ifs with h_ki h_kj
        ·
          linarith
        ·
          linarith
        ·
          rfl
      else
        simp at h_k
        split_ifs with h_ki h_kj
        ·
          simp [h_ki]
          rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength (by linarith) (by linarith)]
        ·
          simp [h_kj]
          rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength.left (by linarith) (by linarith)]
        ·
          simp_all
          rw [GetSwap.eq.Ite.of.GtLength.GtLength.GtLength (by simp_all) (by simp_all)]
          ·
            have h_ki := NeSub.of.Ne_Add.Ge.left (by assumption) h_ki
            have h_kj := NeSub.of.Ne_Add.Ge.left (by assumption) h_kj
            simp_all
          ·
            apply LtSub.of.Lt_Add.Ge (by assumption) (by assumption)
    else
      simp at h
      repeat rw [GetElem.eq.None.of.Ge_Length]
      ·
        rw [LengthAppend.eq.AddLengthS]
        rwa [LengthSwap.eq.Length]
      ·
        rw [LengthSwap.eq.Length]
        rwa [LengthAppend.eq.AddLengthS]
  else
    rw [NotAnd.is.OrNotS] at h
    simp at h
    obtain h | h := h
    ·
      repeat rw [EqSwap.of.Ge_Length.left (by simp_all)]
    ·
      repeat rw [EqSwap.of.Ge_Length (by simp_all)]


-- created on 2025-06-10
-- updated on 2025-06-11
