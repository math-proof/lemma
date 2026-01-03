import sympy.sets.fancyset
import sympy.matrices.expressions.special
import sympy.tensor.stack
import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (A  : Tensor ℝ [n, n])
  (V  : Tensor ℝ [n, d_z]) :
-- imply
  let mask := (1 : Tensor ℝ* [n, n]).band_part (l - 1) (u - 1)
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + (mask - 1) * Hyperreal.omega).softmax @ V = [i < n] A[i, i + 1 - l : n ⊓ i + u].softmax @ V[i + 1 - l : n ⊓ i + u] := by
-- proof
  sorry


-- created on 2026-01-02
