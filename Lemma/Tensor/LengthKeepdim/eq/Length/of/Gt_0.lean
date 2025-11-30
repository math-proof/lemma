import sympy.tensor.functions
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0
open Tensor List


@[main]
private lemma main
  {d : ℕ}
  {s : List ℕ}
-- given
  (h_dim : d > 0)
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim.length = X.length := by
-- proof
  cases s with
  | nil =>
    simp [Tensor.length]
  | cons s₀ s =>
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    simp
    rw [Length.eq.Get_0.of.GtLength_0] <;>
    ·
      simp [EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0 h_dim s]


-- created on 2025-10-09
