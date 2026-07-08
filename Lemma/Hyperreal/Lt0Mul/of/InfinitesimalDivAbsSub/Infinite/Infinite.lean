import Lemma.Int.AbsNeg.eq.Abs
import Lemma.Int.SubNeg_Neg.eq.NegSub
import Lemma.Hyperreal.Gt_0.of.Gt_0.InfinitesimalDivAbsSub.Infinite.Infinite
import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Int.Lt0Mul.of.Lt_0.Lt_0
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
open Hyperreal Int Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a → ∞)
  (h_b : b → ∞)
  (h : (|a - b| / (|a| + |b| + 1)) → 0) :
-- imply
  a * b > 0 := by
-- proof
  if h_a_0 : a > 0 then
    apply Lt0Mul.of.Gt_0.Gt_0 h_a_0
    apply Gt_0.of.Gt_0.InfinitesimalDivAbsSub.Infinite.Infinite h_a h_b h h_a_0
  else if h_a_0 : a < 0 then
    apply Lt0Mul.of.Lt_0.Lt_0 h_a_0
    have h_a_0 := GtNeg_0.of.Lt_0 h_a_0
    have h_a := InfiniteNeg.of.Infinite h_a
    have h_b := InfiniteNeg.of.Infinite h_b
    have h : (|-a - -b| / (|-a| + |-b| + 1)) → 0 := by
      rw [SubNeg_Neg.eq.NegSub]
      repeat rw [AbsNeg.eq.Abs]
      assumption
    have h_b_0 := Gt_0.of.Gt_0.InfinitesimalDivAbsSub.Infinite.Infinite h_a h_b h h_a_0
    simp at h_b_0
    assumption
  else
    have : a = 0 := by linarith
    have h_a_ne_0 := Ne_0.of.Infinite h_a
    contradiction


-- created on 2025-12-22
