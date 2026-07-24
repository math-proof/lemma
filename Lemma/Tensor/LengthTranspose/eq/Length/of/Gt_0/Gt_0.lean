import Lemma.List.Permute.of.Eq.EqValS.Eq
import Lemma.List.EqSwap
import Lemma.List.EqSwap.of.OrLeSLength
import Lemma.List.Swap
import Lemma.List.Swap.eq.PermutePermute.of.Lt.GtLength
import Lemma.Tensor.LengthCast.eq.Length.of.Eq
import Lemma.Tensor.LengthPermute.eq.Length.of.Ge_0.GtVal_0
import Lemma.Tensor.LengthPermute.eq.Length.of.Lt0Add.GtVal_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
-- given
  (h_i : i > 0)
  (h_j : j > 0)
  (X : Tensor α s) :
-- imply
  (X.transpose i j).length = X.length := by
-- proof
  unfold Tensor.transpose
  simp
  split_ifs with h_eq h_ge h_gt
  ·
    rw [LengthCast.eq.Length.of.Eq]
    subst h_eq
    rw [EqSwap]
  ·
    rw [LengthCast.eq.Length.of.Eq]
    rwa [EqSwap.of.OrLeSLength]
  ·
    rw [LengthCast.eq.Length.of.Eq]
    ·
      rw [LengthPermute.eq.Length.of.Lt0Add.GtVal_0]
      ·
        rw [LengthPermute.eq.Length.of.Ge_0.GtVal_0]
        ·
          simpa [h_gt]
        ·
          simp [h_gt]
          grind
      ·
        simpa [h_gt]
      ·
        simp [h_gt]
        grind
    ·
      simp [h_gt]
      rw [Swap]
      rw [Swap.eq.PermutePermute.of.Lt.GtLength]
      ·
        repeat rw [Permute.of.Eq.EqValS.Eq]
        ·
          rfl
        ·
          simp [h_gt]
        ·
          simp [h_gt]
        ·
          rfl
        ·
          rfl
      ·
        aesop
      ·
        grind
  ·
    rw [LengthCast.eq.Length.of.Eq]
    ·
      rw [LengthPermute.eq.Length.of.Lt0Add.GtVal_0]
      ·
        rw [LengthPermute.eq.Length.of.Ge_0.GtVal_0]
        ·
          simpa [h_gt]
        ·
          simp [h_gt]
          grind
      ·
        simpa [h_gt]
      ·
        simp [h_gt]
        grind
    ·
      simp [h_gt]
      rw [Swap.eq.PermutePermute.of.Lt.GtLength]
      ·
        repeat rw [Permute.of.Eq.EqValS.Eq]
        ·
          rfl
        ·
          simp [h_gt]
        ·
          simp [h_gt]
        ·
          rfl
        ·
          rfl
      ·
        aesop
      ·
        grind


-- created on 2026-07-03
-- updated on 2026-07-04
