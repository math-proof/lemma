import Lemma.Bool.EqCast.of.SEq
import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Tensor.SumPermute.as.PermuteSum.of.Ge
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
open Bool List Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  -- [Add α] [Zero α]
-- given
  (X : Tensor α [m, n]) :
-- imply
  X.sum 1 = Xᵀ.sum 0 := by
-- proof
  rw [Tensor.T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
  rw [SumCast.eq.Cast_Sum.of.Eq (by simp; erw [Permute__Neg1.eq.Swap.of.GtLength (by grind)])]
  apply Eq_Cast.of.SEq
  simp
  symm
  apply SumPermute.as.PermuteSum.of.Ge (by grind)


-- created on 2026-07-22
