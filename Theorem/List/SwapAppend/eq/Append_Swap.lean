module

public import Theorem.Bool.IffEqS.of.Eq
public import Theorem.List.LengthAppend.eq.AddLengthS
public import Theorem.List.GetSwap.eq.Ite.of.GtLength.GtLength.GtLength
public import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
public import Theorem.Nat.EqSubAdd
public import Theorem.List.GetAppend.eq.Get.of.GtLength
public import Theorem.Nat.LtSub.is.Lt_Add.of.Ge
public import Theorem.Nat.Ne_Sub.of.NeAdd.Ge
public import Theorem.List.GetSwap.eq.Get.of.GtLengthSwap.GtLength
public import Theorem.List.GetElem.eq.None.of.LeLength
public import Theorem.Bool.NotAnd.is.OrNotS
public import Theorem.List.EqSwap.of.LeLength

public import Theorem.List.LengthSwap.eq.Length
public section

open List Bool Nat


public theorem List.SwapAppend.eq.Append_Swap
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
      repeat rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by linarith) (by simp_all)]
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
          rw [GetSwap.eq.Get.of.GtLengthSwap.GtLength (by linarith) (by linarith)]
        ·
          simp [h_kj]
          rw [GetSwap.eq.Get.of.GtLengthSwap.GtLength.left (by linarith) (by linarith)]
        ·
          simp_all
          rw [GetSwap.eq.Ite.of.GtLength.GtLength.GtLength (by simp_all) (by simp_all)]
          ·
            have h_ki := Ne_Sub.of.NeAdd.Ge.left (by assumption) (Ne.symm h_ki)
            have h_kj := Ne_Sub.of.NeAdd.Ge.left (by assumption) (Ne.symm h_kj)
            simp_all [eq_comm]
          ·
            apply LtSub.of.Lt_Add.Ge (by assumption) (by assumption)
    else
      simp at h
      repeat rw [GetElem.eq.None.of.LeLength]
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
      repeat rw [EqSwap.of.LeLength.left (by simp_all)]
    ·
      repeat rw [EqSwap.of.LeLength (by simp_all)]


-- created on 2025-06-10
-- updated on 2025-06-11
