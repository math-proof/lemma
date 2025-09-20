import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Data0.eq.Zero
import Lemma.Algebra.Div0'0.eq.Zero
open Tensor Algebra


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor α s) / (0 : Tensor α s) = (0 : Tensor α s) := by
-- proof
  apply Eq.of.EqDataS
  rw [Data0.eq.Zero]
  simp [HDiv.hDiv]
  simp [Div.div]
  rw [Data0.eq.Zero]
  apply Div0'0.eq.Zero


-- created on 2025-09-04
