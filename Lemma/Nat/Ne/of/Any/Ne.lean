import sympy.Basic
import torch.Tensor


@[main]
private lemma main
  {A B : Tensor α (n :: s)}
-- given
  (h : ∃ i : Fin n, A[i] ≠ B[i]) :
-- imply
  A ≠ B := by
-- proof
  intro hAB
  obtain ⟨i, hi⟩ := h
  exact hi (by rw [hAB])


-- created on 2023-05-01
