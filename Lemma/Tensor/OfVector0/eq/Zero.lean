import torch.Tensor.Basic
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.Flatten0.eq.Zero
open Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) (n : ℕ) :
-- imply
  Tensor.OfVector (0 : List.Vector (Tensor α s) n) = 0 := by
-- proof
  exact Eq.of.EqDataS (by
    simp only [Tensor.OfVector]
    rw [Vector.EqMap0_0.of.EqUFn_0 (Tensor.data : Tensor α s → List.Vector α s.prod) (by rfl)]
    exact Vector.Flatten0.eq.Zero n s.prod)


-- created on 2026-09-16
