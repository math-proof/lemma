import sympy.tensor.tensor
import Lemma.Tensor.GetCast.eq.Get.of.Eq.Lt
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.LengthSlice.eq.Min
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.EqGetIndices.of.Lt_Min
import Lemma.Nat.Eq.of.EqValS
open Tensor Vector List Nat


@[main]
private lemma main
-- given
  (X : Tensor α (s₀ :: s))
  (h : i < n ⊓ s₀) :
-- imply
  have : i < X.length := by aesop
  have : i < (⟨0, n, 1⟩ : Slice).length s₀ := by simp_all [LengthSlice.eq.Min]
  X[:n][i] = X[i] := by
-- proof
  intro hi
  unfold Tensor.getSlice
  simp
  simp [GetElem.getElem]
  rw [Tensor.get]
  rw [Tensor.toVector]
  simp [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.Lt.fin _ (by simp)]
  ·
    have h_s₀ : s₀ = X.length := by
      rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
      simp
    simp
    apply Eq.of.EqDataS
    simp
    rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin]
    rw [EqUnflattenFlatten]
    rw [GetMap.eq.UFnGet.of.Lt.fin]
    congr
    apply Eq.of.EqValS (b := ⟨i, hi⟩)
    simp
    rw [EqGetIndices.of.Lt_Min.fin]
    .
      rwa [← h_s₀]
    .
      simp only [LengthSlice.eq.Min]
      rwa [← h_s₀]
  ·
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    simp_all [LengthSlice.eq.Min]


@[main]
private lemma fin
-- given
  (X : Tensor α (s₀ :: s))
  (h : i < n ⊓ s₀) :
-- imply
  have h_i : i < X.length := by aesop
  have h_i' : i < (⟨0, n, 1⟩ : Slice).length s₀ := by simp_all [LengthSlice.eq.Min]
  X[:n].get ⟨i, h_i'⟩ = X.get ⟨i, h_i⟩ := by
-- proof
  apply main
  assumption


-- created on 2025-08-04
