import torch.Tensor.reshape
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Repeat0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Nat.EqMulDiv.of.Dvd
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.prod ∣ s'.prod) :
-- imply
  (0 : Tensor α s).reshape s' h = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.reshape, EqData0'0, Repeat0.eq.Zero]
  rw [EqCast_0'0.of.Eq (Nat.EqMulDiv.of.Dvd h)]


-- created on 2026-09-16
