import sympy.tensor.tensor
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
open Tensor


@[main]
private lemma main
  {A : Tensor α (n :: s₀)}
  {B : Tensor α (n :: s₁)}
-- given
  (h₀ : s₀ = s₁)
  (h₁ : ∀ i : Fin n, A[i] ≃ B[i]) :
-- imply
  A ≃ B :=
-- proof
  SEq.of.All_SEqGetS.Eq.Eq rfl h₀ h₁

-- created on 2025-10-07
