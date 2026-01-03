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
  {β ζ : Tensor ℕ [n]}
-- given
  (A  : Tensor ℝ [n, n])
  (V  : Tensor ℝ [n, d_z])
  (i : Fin n) :
-- imply
  let mask := (1 : Tensor ℝ* [n, n]).band_part (l - 1) (u - 1)
  let A : Tensor ℝ* [n, n] := A
  let Q := (A + (mask - 1) * Hyperreal.omega).softmax
  let V' : Tensor ℝ* [n, d_z] := V
  Q @ V' ≃ [i < n] (
    let A'' := A[i][i + 1 - l : n ⊓ i + u]
    let Q' := A''.softmax
    let V' := V'[i + 1 - l : n ⊓ i + u]
    Q' @ V'
  ) := by
-- proof
  sorry


-- created on 2026-01-02
