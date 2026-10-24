/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/ZagierMatrixInverse.lean -/


import sympy.atlas.LinearAlgebra.Matrix.ZagierMatrixInverse
import Lemma.Matrix.ZagierMatrixInverse

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierMatrix K

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierInverseP K

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierInverseQ K

example := MetaMathlibExt.zagierInverseP_eq_zagierInverseQ 3 (by decide)

example := MetaMathlibExt.zagierMatrix_mul_zagierInverseP 3 (by decide)

example := MetaMathlibExt.zagierInverseP_mul_zagierMatrix 3 (by decide)

example := (MetaMathlibExt.zagier_matrix_inverse 3 (by decide)).2.2
