import Lemma.Tensor.Slice.of.Eq
import Lemma.Tensor.Get.of.Eq.Lt
open Tensor


@[main]
private lemma main
  {n : ℕ}
  {X Y : Tensor α ((n + 1) :: s)}
-- given
  (h : X = Y) :
-- imply
  have : n < X.length := by simp [Tensor.length]
  have : n < Y.length := by simp [Tensor.length]
  X[:n] = Y[:n] ∧ X[n] = Y[n] := by
-- proof
  constructor
  ·
    apply Slice.of.Eq h
  ·
    apply Get.of.Eq.Lt
    assumption


-- created on 2025-09-29
