import Lemma.Tensor.Sum.eq.FromVectorMapToVector
open Tensor


@[main, cast]
private lemma main
  [Add α] [Zero α]
-- given
  (h_s : s.length > 0)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.sum (d + 1) ≃ Tensor.fromVector (X.toVector.map (·.sum d)) := by
-- proof
  match s with
  | .nil =>
    contradiction
  | s₀ :: s =>
    rw [Sum.eq.FromVectorMapToVector]
    rfl


-- created on 2026-07-22
