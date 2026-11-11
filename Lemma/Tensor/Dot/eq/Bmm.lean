import Lemma.Tensor.Einsum.eq.Bmm
import Def.Data.Tensor.Bmm
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n]) :
-- imply
  A ⬝ᵥ B = A.bmm B := by
-- proof
  simp [Dot.dot]
  rw [Einsum.eq.Bmm]
  rfl


-- created on 2026-07-21
