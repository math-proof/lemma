import Lemma.Set.Frac.in.Ico
import Lemma.Rat.Sub_Mul_FloorDiv.eq.Mul_Frac
import Lemma.Set.Ge.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Nat.LtMulS.of.Lt.Gt_0
import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.FMod.ge.Zero.of.Gt_0
import Lemma.Int.LtFMod.of.Gt_0
open Set Rat Nat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {d : α}
-- given
  (h : d > 0)
  (n : α) :
-- imply
  n - d * ⌊n / d⌋ ∈ Ico 0 d := by
-- proof
  rw [Sub_Mul_FloorDiv.eq.Mul_Frac h]
  have h_frac := Frac.in.Ico (x := n / d)
  apply In_Ico.of.Le.Lt
  ·
    have := Ge.of.In_Ico h_frac
    simpa [mul_comm] using GeMulS.of.Ge.Gt_0 this h
  ·
    have := Lt.of.In_Ico h_frac
    simpa [mul_comm, one_mul] using LtMulS.of.Lt.Gt_0 this h


-- created on 2026-08-03
