/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/GaussPivot.lean -/


import Mathlib.Tactic.NormNum
import Def.LinearAlgebra.Matrix.GaussPivot.Part2
import Lemma.Matrix.GaussPivot
open MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted


-- Swapping row `1` into row `0` supplies the missing pivot in the first column.
example :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    ∃ P : Matrix (Fin 2) (Fin 2) ℚ, P.IsLowerTriangular ∧
      (∀ i, P.diag i = 1) ∧
        ∀ i > 0, (P * A.submatrix (Equiv.swap 0 1) id) i 0 = 0 := by
  dsimp only
  apply gauss_pivot_elim_step
  norm_num

-- Both endpoint APIs handle the same matrix whose first row has no first-column pivot.
example :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    (∃ (L : Matrix (Fin 2) (Fin 2) ℚ) (σ : Equiv.Perm (Fin 2)),
      L.IsLowerTriangular ∧ (∀ i, L.diag i = 1) ∧
        (L * A.submatrix σ id).IsRowEchelon) ∧
      ∃ (ops : List (Matrix (Fin 2) (Fin 2) ℚ)) (σ : Equiv.Perm (Fin 2)),
        (∀ M ∈ ops, M.IsLowerTriangular ∧ ∀ i, M.diag i = 1) ∧
          (ops.prod * A.submatrix σ id).IsRowEchelon := by
  dsimp only
  exact ⟨Matrix.exists_unitLowerTriangular_mul_submatrix_isRowEchelon _,
    exists_gauss_elimination_opList _⟩

