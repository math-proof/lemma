import Lemma.Hyperreal.GeSt_0.of.Ge_0
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.StNeg.eq.NegSt
import Lemma.Int.Abs.eq.Neg.of.Le_0
import Lemma.Int.EqAbs.of.Ge_0
open Hyperreal Int


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  |x|.st = |x.st| := by
-- proof
  if h_x : x ≥ 0 then
    have := GeSt_0.of.Ge_0 h_x
    repeat rw [EqAbs.of.Ge_0 (by assumption)]
  else
    simp at h_x
    have := LeSt_0.of.Le_0 (by linarith)
    repeat rw [Abs.eq.Neg.of.Le_0 (by linarith)]
    rw [StNeg.eq.NegSt]


-- created on 2025-12-21
