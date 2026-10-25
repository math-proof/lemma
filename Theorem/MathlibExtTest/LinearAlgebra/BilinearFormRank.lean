/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearFormRank.lean -/


import Def.LinearAlgebra.BilinearFormRank
import Lemma.Matrix.BilinearFormRank


noncomputable section

-- A non-permutation rescaling has the same full rank as the standard basis.
example :
    let b₂ := (Pi.basisFun ℚ (Fin 2)).unitsSMul
      (fun _ ↦ Units.mk0 (2 : ℚ) (by norm_num))
    let B : LinearMap.BilinForm ℚ (Fin 2 → ℚ) :=
      Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℚ)
    (LinearMap.BilinForm.toMatrix b₂ B).rank = 2 := by
  dsimp only
  rw [LinearMap.BilinForm.rank_toMatrix_eq_rank_toMatrix
    _ (Pi.basisFun ℚ (Fin 2)) _]
  rw [LinearMap.BilinForm.toMatrix_basisFun,
    LinearMap.BilinForm.toMatrix'_toBilin', Matrix.rank_one]
  simp

-- The frozen theorem computes the dot-product rank in a rescaled basis.
example :
    let b₂ := (Pi.basisFun ℚ (Fin 2)).unitsSMul
      (fun _ ↦ Units.mk0 (2 : ℚ) (by norm_num))
    let B : LinearMap.BilinForm ℚ (Fin 2 → ℚ) :=
      Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℚ)
    MathlibExt.LinearAlgebra.BilinearFormRankWanted.bilinFormRank b₂ B = 2 := by
  dsimp only
  rw [MathlibExt.LinearAlgebra.BilinearFormRankWanted.bilinFormRank_basis_independent
    _ (Pi.basisFun ℚ (Fin 2)) _]
  rw [LinearMap.BilinForm.toMatrix_basisFun,
    LinearMap.BilinForm.toMatrix'_toBilin', Matrix.rank_one]
  simp

end
