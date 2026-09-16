import torch.Tensor.resize
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.Resize0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (d : Fin s.length) (n : ℕ) :
-- imply
  (0 : Tensor α s).resize d n = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.resize, EqData0'0, EqSplitAt0_0]
  rw [EqMap0_0.of.EqUFn_0
    (fun x : List.Vector α (s.drop d).prod =>
      x.resize (n * (s.drop d.succ).prod)) (Resize0.eq.Zero _ _)]
  simp [Flatten0.eq.Zero]
  rw [EqCast_0'0.of.Eq (by simp [List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength])]


-- created on 2026-09-16
