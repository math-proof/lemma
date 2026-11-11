import Instance.LinearAlgebra.Matrix.Matmul
import Instance.Data.Vector.Basic.Dot


@[path]
private lemma left
  [Mul α] [Add α] [Zero α]
  {X Y : Tensor α s}
  {lhs : Tensor α s'}
-- given
  (h : X = Y) :
-- imply
  lhs ⬝ᵥ X = lhs ⬝ᵥ Y := by
-- proof
  rw [h]


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
  {X Y : Tensor α s}
  {rhs : Tensor α s'}
-- given
  (h : X = Y) :
-- imply
  X ⬝ᵥ rhs = Y ⬝ᵥ rhs := by
-- proof
  rw [h]


-- created on 2020-08-16
-- updated on 2026-10-26
