import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Determinant

/--
[det_leibniz_column](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Determinant.lean)
-/
@[path]
lemma det_leibniz_column
  [DecidableEq n]
  [Fintype n]
  [CommRing R]
  {M : Matrix n n R} :
-- imply
  M.det = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) • ∏ i, M i (σ i) := by
-- proof
  rw [← Matrix.det_transpose, Matrix.det_apply]
  congr 1

end Determinant


-- created on 2026-10-23
-- updated on 2026-10-28
