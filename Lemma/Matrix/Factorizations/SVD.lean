import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Factorizations.SVD
open Matrix
open scoped ComplexOrder


/--
[exists_unitaryGroup_diagonal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/SVD.lean)
-/
@[path]
private lemma exists_unitaryGroup_diagonal_nonneg_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ} :
-- imply
  ∃ (U V : Matrix.unitaryGroup n ℂ) (σ : n → ℝ), (∀ i, 0 ≤ σ i) ∧
    A = (U : Matrix n n ℂ) * diagonal (fun i => (σ i : ℂ)) * star (V : Matrix n n ℂ) := by
-- proof
  apply Matrix.exists_unitaryGroup_diagonal_nonneg A


-- created on 2026-10-20
