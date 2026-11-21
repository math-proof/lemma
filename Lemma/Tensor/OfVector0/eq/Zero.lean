import Instance.Data.Tensor.Defs.Part2
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.Flatten0.eq.Zero
open Tensor Vector


@[path]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) (n : ℕ) :
-- imply
  Tensor.OfVector (0 : List.Vector (Tensor α s) n) = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.OfVector]
  rw [EqMap0_0.of.EqUFn_0 (Tensor.data : Tensor α s → List.Vector α s.prod) (by rfl)]
  apply Flatten0.eq.Zero


-- created on 2026-09-16
-- updated on 2026-11-21
