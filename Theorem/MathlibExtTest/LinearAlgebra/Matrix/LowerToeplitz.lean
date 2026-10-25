/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/LowerToeplitz.lean -/


import Mathlib.Tactic.NormNum
import Def.LinearAlgebra.Matrix.LowerToeplitz
import Lemma.Matrix.LowerToeplitz
import Def.MathlibExtTest.LinearAlgebra.Matrix.LowerToeplitz


/-- Below-diagonal entry over `ℕ`: `(2, 0)` reads `testSeqN (2 - 0) = 3`. -/
example : Matrix.lowerToeplitz testSeqN 2 0 = 3 := by
  rw [Matrix.lowerToeplitz_apply_of_le _ (by norm_num : 0 ≤ 2)]
  rfl

/-- Above-diagonal entry over `ℕ`: `(0, 2)` vanishes. -/
example : Matrix.lowerToeplitz testSeqN 0 2 = 0 :=
  Matrix.lowerToeplitz_apply_of_gt _ (by norm_num : 0 < 2)

/-- Diagonal entry over `ℕ`: `(1, 1)` reads `testSeqN 0 = 1`. -/
example : Matrix.lowerToeplitz testSeqN 1 1 = 1 := by
  rw [Matrix.lowerToeplitz_apply_diag]
  rfl

/-- Below-diagonal entry over `ℤ`: `(2, 0)` reads `testSeqZ (2 - 0) = 3`. -/
example : Matrix.lowerToeplitz testSeqZ 2 0 = 3 := by
  rw [Matrix.lowerToeplitz_apply_of_le _ (by norm_num : 0 ≤ 2)]
  norm_num [testSeqZ]

/-- Above-diagonal entry over `ℤ`: `(0, 2)` vanishes. -/
example : Matrix.lowerToeplitz testSeqZ 0 2 = 0 :=
  Matrix.lowerToeplitz_apply_of_gt _ (by norm_num : 0 < 2)

/-- Diagonal entry over `ℤ`: `(1, 1)` reads `testSeqZ 0 = 1`. -/
example : Matrix.lowerToeplitz testSeqZ 1 1 = 1 := by
  rw [Matrix.lowerToeplitz_apply_diag]
  norm_num [testSeqZ]

#print axioms Matrix.lowerToeplitz
#print axioms Matrix.lowerToeplitz_apply_of_le
#print axioms Matrix.lowerToeplitz_apply_of_gt
#print axioms Matrix.lowerToeplitz_apply_diag

