/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/UpperHessenbergMatrix.lean -/
module

public import Def.LinearAlgebra.Matrix.UpperHessenbergMatrix

public section

namespace Matrix

example (n : ℕ) : IsUpperHessenberg (1 : Matrix (Fin n) (Fin n) ℤ) := by
  intro i j hij
  simp only [one_apply]
  split_ifs
  · omega
  · rfl

end Matrix
