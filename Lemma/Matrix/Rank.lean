import Mathlib
import Initialize.Tactic.Attr.Basic


namespace LinearAlgebra

/--
[rank_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/LinearAlgebra.lean)
-/
@[path]
lemma rank_transpose
  [Field F]
  [Fintype m]
  [Fintype n]
  [DecidableEq m]
  [DecidableEq n]
  {M : Matrix m n F} :
-- imply
  M.rank = Mᵀ.rank :=
-- proof
  (Matrix.rank_transpose M).symm

end LinearAlgebra


-- created on 2026-10-23
