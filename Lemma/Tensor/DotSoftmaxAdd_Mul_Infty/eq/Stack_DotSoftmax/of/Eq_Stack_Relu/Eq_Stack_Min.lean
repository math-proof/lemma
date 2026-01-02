import sympy.sets.fancyset
import sympy.tensor.stack
import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
  {β ζ : Tensor ℕ [n]}
-- given
  (h₀ : β = [i < n] (i + 1 - l : ℕ))
  (h₁ : ζ = [i < n] (n ⊓ i + u))
  (A  : Tensor ℝ [n, n])
  (V  : Tensor ℝ [n, d_z]) :
-- imply
  (A + Hyperreal.omega * (BandPart (l - 1) (u - 1) Ones [n, n] - 1)).softmax @ V = [i < n] (softmax A[i][i + 1 - l : n ⊓ i + u] @ V[i + 1 - l : n ⊓ i + u]) := by
-- proof
  sorry


-- created on 2026-01-02
