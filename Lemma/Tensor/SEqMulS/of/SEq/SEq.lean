import stdlib.SEq
import sympy.tensor.tensor


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
  sorry


-- created on 2025-12-01
