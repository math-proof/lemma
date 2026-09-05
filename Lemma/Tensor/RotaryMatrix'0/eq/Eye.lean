import Lemma.Fin.EqOfSplitToSplit
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetRotaryMatrix'.eq.GetRotaryMatrix
import Lemma.Tensor.RotaryMatrix0.eq.Eye
import sympy.matrices.expressions.special
open Fin Nat Tensor


@[main]
private lemma main :
-- imply
  (0 : Tensor ℝ [d]).rotaryMatrix' = Tensor.eye (d + d) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (GetRotaryMatrix'.eq.GetRotaryMatrix (0 : Tensor ℝ [d]) i j).trans
  apply (congrArg (fun t : Tensor ℝ [d + d, d + d] => t[i.toSplit][j.toSplit]) RotaryMatrix0.eq.Eye).trans
  apply (GetEye.eq.Delta.fin (α := ℝ) i.toSplit j.toSplit).trans
  apply Eq.trans _ (GetEye.eq.Delta.fin (α := ℝ) i j).symm
  apply congrArg (fun n : ℕ => (↑n : Tensor ℝ []))
  simp [Delta.eq.Ite]
  if h : i.toSplit = j.toSplit then
    have hij : i = j := by
      apply Eq.trans (EqOfSplitToSplit i).symm
      apply Eq.trans (congrArg (·.ofSplit) h)
      apply EqOfSplitToSplit
    simp [hij]
  else
    have hij : i ≠ j := by
      intro hij
      apply h
      simp [hij]
    simp [h, hij]


-- created on 2026-09-05
