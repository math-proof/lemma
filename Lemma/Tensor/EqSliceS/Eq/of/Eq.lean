import Lemma.Tensor.EqSliceS.of.Eq
import Lemma.Tensor.EqGetS.of.Eq.Lt
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
    apply EqSliceS.of.Eq h
  ·
    apply EqGetS.of.Eq.Lt
    assumption


-- created on 2025-09-29
