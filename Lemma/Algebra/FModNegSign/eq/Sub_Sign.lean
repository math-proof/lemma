import Lemma.Algebra.Lt.ou.Eq.ou.Gt
import Lemma.Algebra.Sign.eq.Neg1.of.Lt_0
import Lemma.Algebra.EqSign_1.of.Gt_0
import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.Sub.eq.AddNeg
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.FDiv1.eq.Neg1.of.Lt_0
import Lemma.Algebra.SubNeg
import Lemma.Algebra.EqSubS.is.Eq
import Lemma.Algebra.FDivNeg1.eq.Neg1.of.Gt_0
open Algebra


@[main]
private lemma main
  {d : ℤ} :
-- imply
  (-sign d).fmod d = d - sign d := by
-- proof
  rcases Lt.ou.Eq.ou.Gt d 0 with h_d | h_d | h_d
  ·
    have := Sign.eq.Neg1.of.Lt_0 h_d
    rw [this]
    simp
    rw [FMod.eq.Sub_MulFDiv]
    rw [Sub.eq.AddNeg]
    apply EqAddS.of.Eq 1
    rw [FDiv1.eq.Neg1.of.Lt_0 h_d]
    simp
  ·
    rw [h_d]
    norm_num
  ·
    have := EqSign_1.of.Gt_0 h_d
    rw [this]
    rw [FMod.eq.Sub_MulFDiv]
    rw [SubNeg.comm]
    apply EqSubS.of.Eq (d := 1)
    rw [FDivNeg1.eq.Neg1.of.Gt_0 h_d]
    simp


-- created on 2025-03-30
