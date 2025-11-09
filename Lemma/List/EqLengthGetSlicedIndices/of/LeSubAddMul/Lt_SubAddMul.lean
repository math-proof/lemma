import Lemma.Int.SubSub
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Gt_0
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
open Int List Nat Rat


@[main]
private lemma main
  {j' : Fin d}
-- given
  (h_start : j < n * d + j - j')
  (h_stop : n * d + j - j' ≤ N) :
-- imply
  have h_step := Gt_0 j'
  (Nat.sliced_indices h_start h_stop h_step).length = n := by
-- proof
  intro h_step
  rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]
  rw [CoeSub.eq.SubCoeS.of.Ge (by omega)]
  simp [SubSub.comm]
  simp [EqToNatCeilDivSubMul.of.Lt]


-- created on 2025-11-09
