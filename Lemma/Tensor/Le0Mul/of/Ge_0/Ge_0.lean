import Lemma.Vector.Le0Mul.of.Ge_0.Ge_0
import sympy.tensor.tensor
open Vector


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulMono α]
  {A B : Tensor α s}
-- given
  (h₀ : A ≥ 0)
  (h₁ : B ≥ 0) :
-- imply
  A * B ≥ 0 :=
-- proof
  Le0Mul.of.Ge_0.Ge_0 h₀ h₁


-- created on 2026-07-27
