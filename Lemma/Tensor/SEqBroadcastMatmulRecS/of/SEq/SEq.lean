import Lemma.Bool.SEq.is.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α (s_A ++ [m, t])}
  {A' : Tensor α (s_A' ++ [m, t])}
  {B : Tensor α (s_B ++ [t, k])}
  {B' : Tensor α (s_B' ++ [t, k])}
-- given
  (h : s_A.length = s_B.length)
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  have h_A' : s_A = s_A' := by
    have := h_A.left
    simp at this
    assumption
  have h_B' : s_B = s_B' := by
    have := h_B.left
    simp at this
    assumption
  A.broadcast_matmul_rec B (by grind) ≃ A'.broadcast_matmul_rec B' (by grind) := by
-- proof
  intro h_A' h_B'
  have h_A' := h_A'
  have h_B' := h_B'
  subst h_A' h_B'
  have h_A := Eq.of.SEq h_A
  have h_B := Eq.of.SEq h_B
  subst h_A h_B
  rfl


-- created on 2026-01-11
