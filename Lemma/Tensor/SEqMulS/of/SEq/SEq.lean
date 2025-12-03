import Lemma.Bool.SEq.is.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Mul α]
  {A B : Tensor α s}
  {A' B' : Tensor α s'}
-- given
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  A * B ≃ A' * B' := by
-- proof
  have h_s := h_A.left
  subst h_s
  have h_A := Eq.of.SEq h_A
  have h_B := Eq.of.SEq h_B
  subst h_A h_B
  rfl


-- created on 2025-12-01
-- updated on 2025-12-03
