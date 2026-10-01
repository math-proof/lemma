import torch.nn.functional.relu
import sympy.Basic


@[main]
private lemma main
  {n l u i : ℤ}
  {β ζ : ℤ → ℤ}
-- given
  (h₀ : ∀ i, β i = relu (i - l + 1))
  (h₁ : ∀ i, ζ i = min (i + u) n) :
-- imply
  ζ i - β i ≤ min n (l + u - 1) := by
-- proof
  rw [h₀, h₁]
  unfold relu
  simp only [min_def, max_def]
  split_ifs <;> omega


-- created on 2021-12-23
