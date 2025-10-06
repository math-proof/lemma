import Lemma.Tensor.Eq_Stack
open Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X ≃ [i < X.length] X[i] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons s₀ s =>
    conv in X =>
      rw [Eq_Stack X]
    constructor <;>
      congr


-- created on 2025-07-02
