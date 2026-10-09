import sympy.Basic
import torch.Tensor
open Tensor


@[path]
private lemma main
  {n : ℕ}
  {a b : ℤ}
  {x y : Tensor ℝ [n]}
-- given
  (_ : Set.Ico a b ⊆ Set.Ico (0 : ℤ) n)
  (h : x = y) :
-- imply
  x.getSlice ⟨a, b, 1⟩ = y.getSlice ⟨a, b, 1⟩ := by
-- proof
  rw [h]


-- created on 2026-10-08
