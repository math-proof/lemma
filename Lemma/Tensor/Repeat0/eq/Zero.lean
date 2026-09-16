import torch.Tensor.repeat
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.Repeat0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (d : Fin s.length) (n : ℕ) :
-- imply
  (0 : Tensor α s).repeat d n = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.repeat, EqData0'0, EqSplitAt0_0]
  rw [EqMap0_0.of.EqUFn_0 (fun x : List.Vector α (s.drop d).prod => x.repeat n) (Repeat0.eq.Zero _ _)]
  simp [Flatten0.eq.Zero]
  rw [EqCast_0'0.of.Eq (by simp [List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength])]


-- created on 2026-09-16
