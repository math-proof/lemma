import Mathlib.Analysis.Matrix.LDL

/-! Cholesky decomposition: existence of a lower-triangular factor with positive diagonal
(from Mathlib's LDL decomposition) and uniqueness via the py Cholesky recursion `IsCholeskyRec`.
-/

open Matrix
open scoped ComplexOrder


/-- py `eq_piece` of the Cholesky algorithm:
`L[i, j] = (A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j]` for `j < i`,
`L[i, i] = sqrt(A[i, i] - ‖L[i, :i]‖²)`, and `0` above the diagonal. -/
def IsCholeskyRec {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (A L : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ i j, L i j =
    if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j
    else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : 𝕜)
    else 0


-- created on 2026-09-27
