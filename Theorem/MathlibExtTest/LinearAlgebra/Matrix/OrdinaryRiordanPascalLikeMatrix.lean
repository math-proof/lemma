/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/OrdinaryRiordanPascalLikeMatrix.lean -/
module

public import Def.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import Theorem.Matrix.OrdinaryRiordanPascalLikeMatrix

public section

namespace MetaMathlibExt

example : ordinaryRiordanPascalLikeMatrix 0 0 0 = 1 := by decide

example : ordinaryRiordanPascalLikeMatrix 2 1 1 = 3 := by decide

example : ordinaryRiordanPascalLikeMatrix 3 1 1 = 5 := by decide

end MetaMathlibExt
