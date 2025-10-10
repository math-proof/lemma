import stdlib.SEq
import sympy.tensor.Basic
import Lemma.Tensor.Unsqueeze.as.UnsqueezeCast.of.Le_Length.Eq
import Lemma.Tensor.SEqUnsqueeze.of.Gt_Length
import Lemma.Bool.SEq.of.SEq.SEq
open Tensor Bool


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_s : s = s')
  (X : Tensor α s) :
-- imply
  X.unsqueeze d ≃ (cast (congrArg (Tensor α) h_s) X).unsqueeze d := by
-- proof
  by_cases h_d : d ≤ s.length
  ·
    apply Unsqueeze.as.UnsqueezeCast.of.Le_Length.Eq h_s h_d
  ·
    simp at h_d
    have := SEqUnsqueeze.of.Gt_Length h_d X
    apply SEq.trans this
    have := SEqUnsqueeze.of.Gt_Length (h_s ▸ h_d) (cast (congrArg (Tensor α) h_s) X)
    apply SEq.of.SEq.SEq _ this
    aesop


-- created on 2025-10-10
