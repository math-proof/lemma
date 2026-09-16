import torch.Tensor.permute
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Tensor.EqTensor0'0
import Lemma.Tensor.PermuteHead0.eq.Zero
import Lemma.Tensor.PermuteTail0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Tensor.EqCast_0'0.of.Eq
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (i : Fin s.length) (d : ℤ) :
-- imply
  (0 : Tensor α s).permute i d = 0 := by
-- proof
  cases d with
  | ofNat d =>
    cases d with
    | zero =>
      simp only [Tensor.permute]
      rw [Tensor.EqCast_0'0.of.Eq (List.EqPermute i).symm]
    | succ d =>
      simp (config := { zeta := true }) only [Tensor.permute]
      split_ifs with h_i0
      · -- i.val = 0
        rw [PermuteHead0.eq.Zero]
        rw [Tensor.EqCast_0'0.of.Eq
          ((List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
            h_i0 (d + 1)).symm)]
      · -- i.val ≠ 0
        simp only [EqData0'0, EqSplitAt0_0, EqMap0_0.of.EqUFn_0, EqTensor0'0,
          PermuteHead0.eq.Zero, Flatten0.eq.Zero]
        apply Eq.of.EqDataS
        exact EqCast_0'0.of.Eq
          (List.ProdPermute.eq.MulProd_ProdAppend i (d + 1)).symm
  | negSucc d =>
    simp (config := { zeta := true }) only [Tensor.permute]
    split_ifs with h_il
    · -- i.val = s.length - 1
      rw [PermuteTail0.eq.Zero]
      rw [Tensor.EqCast_0'0.of.Eq (by
        rw [Int.NegSucc.eq.NegAdd_1]
        exact (List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
          h_il (d + 1)).symm)]
    · -- i.val ≠ s.length - 1
      simp only [EqData0'0, EqSplitAt0_0, EqTensor0'0,
        PermuteTail0.eq.Zero, Flatten0.eq.Zero]
      apply Eq.of.EqDataS
      exact EqCast_0'0.of.Eq (by
        rw [Int.NegSucc.eq.NegCoeAdd_1]
        exact (List.ProdPermute__Neg.eq.MulProd_ProdDrop i (d + 1)).symm)


-- created on 2026-09-16
