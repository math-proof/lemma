import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ordinaryRiordanPascalLikeMatrix_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/OrdinaryRiordanPascalLikeMatrix.lean)
-/
@[path]
lemma ordinaryRiordanPascalLikeMatrix_def
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
