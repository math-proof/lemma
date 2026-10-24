/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/StieltjesMatrix.lean -/


import sympy.atlas.LinearAlgebra.Matrix.StieltjesMatrix

namespace MetaMathlibExt

example {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) :
    stieltjesMatrix a1 b1 a b 0 0 = a1 := by
  simp [stieltjesMatrix]

example {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) :
    stieltjesMatrix a1 b1 a b 2 1 = b := by
  simp [stieltjesMatrix]

example {R : Type*} [AddMonoidWithOne R] (a b lam mu : R) :
    stieltjesMatrixOf a b lam mu 0 0 = a + lam := by
  simp [stieltjesMatrixOf, stieltjesMatrix]

end MetaMathlibExt
