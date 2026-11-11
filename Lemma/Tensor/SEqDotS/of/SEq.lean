import Lemma.Bool.SEq.is.Eq
import Instance.LinearAlgebra.Matrix.Matmul
import Instance.Data.Vector.Basic.Dot
open Bool


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
  {A : Tensor α s_A}
  {B : Tensor α s_B}
-- given
  (h : A ≃ B)
  (X : Tensor α s_X) :
-- imply
  A ⬝ᵥ X ≃ B ⬝ᵥ X := by
-- proof
  have h_s := h.left
  subst h_s
  have h := Eq.of.SEq h
  subst h
  rfl


@[path]
private lemma left
  [Mul α] [Add α] [Zero α]
  {A : Tensor α s_A}
  {B : Tensor α s_B}
-- given
  (h : A ≃ B)
  (X : Tensor α s_X) :
-- imply
  X ⬝ᵥ A ≃ X ⬝ᵥ B := by
-- proof
  have h_s := h.left
  subst h_s
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-01-13
