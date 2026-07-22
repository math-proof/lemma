import Lemma.Tensor.Einsum.eq.Bmm
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n]) :
-- imply
  A @ B = A.bmm B := by
-- proof
  simp [Dot.dot]
  rw [Einsum.eq.Bmm]
  rfl


-- created on 2026-07-21
