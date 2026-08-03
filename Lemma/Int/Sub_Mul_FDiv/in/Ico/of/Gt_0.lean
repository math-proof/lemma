import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.FMod.ge.Zero.of.Gt_0
import Lemma.Int.LtFMod.of.Gt_0
import Lemma.Set.In_Ico.is.Le.Lt
open Int Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n - d * (n // d) ∈ Ico 0 d := by
-- proof
  rw [mul_comm, ← FMod.eq.Sub_MulFDiv]
  apply In_Ico.of.Le.Lt
  ·
    exact FMod.ge.Zero.of.Gt_0 h n
  ·
    exact LtFMod.of.Gt_0 h


-- created on 2026-08-03
