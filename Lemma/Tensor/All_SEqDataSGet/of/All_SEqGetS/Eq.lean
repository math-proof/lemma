import sympy.tensor.tensor
import Lemma.Tensor.SEqDataS.of.SEq
open Tensor


@[main]
private lemma main
  {a : Tensor α (n :: s₀)}
  {b : Tensor α (m :: s₁)}
-- given
  (h₀ : n = m)
  (h : ∀ i : Fin n, a[i] ≃ b[(⟨i, by simp [← h₀]⟩ : Fin m)]) :
-- imply
  ∀ i : Fin n, a[i].data ≃ b[(⟨i, by simp [← h₀]⟩ : Fin m)].data := by
-- proof
  intro i
  apply SEqDataS.of.SEq
  apply h i


-- created on 2025-05-29
