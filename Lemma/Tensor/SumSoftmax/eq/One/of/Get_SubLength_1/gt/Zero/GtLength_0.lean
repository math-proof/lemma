import sympy.tensor.functions
import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[main]
private lemma main
  [ExpPos α]
-- given
  (h_s : s.length > 0)
  (h : s[s.length - 1] > 0)
  (X : Tensor α s) :
-- imply
  (X.softmax).sum = 1 := by
-- proof
  induction s with
  | nil =>
    contradiction
  | cons s₀ s ih =>
    match s with
    | .nil =>
      unfold Tensor.softmax
      unfold Tensor.sum
      simp
      sorry
    | .cons s₁ s' =>
      apply Eq.of.All_EqGetS
      sorry


-- created on 2025-10-07
-- updated on 2025-10-11
