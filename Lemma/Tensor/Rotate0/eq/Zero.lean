import torch.Tensor.permute
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.Transpose0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (k : ℕ) :
-- imply
  (0 : Tensor α s).rotate k = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.rotate]
  simp (config := { zeta := true }) [EqData0'0, EqSplitAt0_0,
    Transpose0.eq.Zero, Flatten0.eq.Zero]
  rw [EqCast_0'0.of.Eq (by
    rw [← List.prod_append, List.AppendDrop__Take.eq.Rotate s k])]


-- created on 2026-09-16
