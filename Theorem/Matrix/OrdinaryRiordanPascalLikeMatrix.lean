module

public import Mathlib
public import Def.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[ordinaryRiordanPascalLikeMatrix_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/OrdinaryRiordanPascalLikeMatrix.lean)
-/
public theorem ordinaryRiordanPascalLikeMatrix_def
  {n k : ℕ}
  {r : ℤ} :
-- imply
  ordinaryRiordanPascalLikeMatrix n k r =
      Finset.sum (Finset.range (k + 1)) fun j =>
        (k.choose j : ℤ) * ((n - j).choose k : ℤ) * r ^ j :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
