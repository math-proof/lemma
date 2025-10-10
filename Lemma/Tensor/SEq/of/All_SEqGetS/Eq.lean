import sympy.tensor.tensor
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
open Tensor


@[main]
private lemma main
  {A : Tensor α (n :: s_A)}
  {B : Tensor α (n :: s_B)}
-- given
  (h₀ : s_A = s_B)
  (h₁ : ∀ i : Fin n, A[i] ≃ B[i]) :
-- imply
  A ≃ B :=
-- proof
  SEq.of.All_SEqGetS.Eq.Eq rfl h₀ h₁


-- created on 2025-10-07
-- updated on 2025-10-10
