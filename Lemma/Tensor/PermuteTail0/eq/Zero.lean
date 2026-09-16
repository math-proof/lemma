import torch.Tensor.permute
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Tensor.EqTensor0'0
import Lemma.Tensor.Rotate0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (size : ℕ) :
-- imply
  (0 : Tensor α s).permuteTail size = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.permuteTail, EqData0'0, EqSplitAt0_0]
  rw [EqMap0_0.of.EqUFn_0 (fun data => ((⟨data⟩ : Tensor α _).rotate _).data)
        (by simp [EqTensor0'0, Tensor.Rotate0.eq.Zero, EqData0'0])]
  simp [Flatten0.eq.Zero]
  rw [EqCast_0'0.of.Eq (by simp [List.prod_append])]


-- created on 2026-09-16
