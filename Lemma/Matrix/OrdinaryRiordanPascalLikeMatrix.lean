import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
open MetaMathlibExt


/--
[ordinaryRiordanPascalLikeMatrix_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/OrdinaryRiordanPascalLikeMatrix.lean)
-/
@[path]
private lemma ordinaryRiordanPascalLikeMatrix_def_eq
  {n k : ℕ}
  {r : ℤ} :
-- imply
  ordinaryRiordanPascalLikeMatrix n k r =
      Finset.sum (Finset.range (k + 1)) fun j =>
        (k.choose j : ℤ) * ((n - j).choose k : ℤ) * r ^ j := by
-- proof
  apply MetaMathlibExt.ordinaryRiordanPascalLikeMatrix_def n k r


-- created on 2026-10-20
