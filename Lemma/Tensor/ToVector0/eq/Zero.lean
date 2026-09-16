import torch.Tensor.Basic
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Tensor.EqTensor0'0
open Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor α s).toVector = 0 := by
-- proof
  have hf : (fun v : List.Vector α (s.drop 1).prod =>
      (⟨cast (by simp) v⟩ : Tensor α s.tail)) 0 = 0 := by
    show (⟨cast _ (0 : List.Vector α (s.drop 1).prod)⟩ : Tensor α s.tail) = 0
    rw [EqCast_0'0.of.Eq (by simp)]
    exact EqTensor0'0 _
  simp only [Tensor.toVector, EqData0'0, EqSplitAt0_0]
  rw [EqMap0_0.of.EqUFn_0 _ hf]
  rw [EqCast_0'0.of.Eq (by rw [List.ProdTake_1.eq.HeadD_1])]


-- created on 2026-09-16
