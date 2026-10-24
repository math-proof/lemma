/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/UpperHessenbergMatrix.lean -/


import sympy.atlas.LinearAlgebra.Matrix.UpperHessenbergMatrix

namespace Matrix

example (n : ℕ) : IsUpperHessenberg (1 : Matrix (Fin n) (Fin n) ℤ) := by
  intro i j hij
  simp only [one_apply]
  split_ifs
  · omega
  · rfl

end Matrix
