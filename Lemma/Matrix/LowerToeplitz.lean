import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.LowerToeplitz
open Matrix


/--
[lowerToeplitz_apply_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
private lemma lowerToeplitz_apply_of_le_eq
  [Zero R]
  {a : ℕ → R}
  {i j : ℕ}
-- given
  (h : j ≤ i) :
-- imply
  lowerToeplitz a i j = a (i - j) := by
-- proof
  apply Matrix.lowerToeplitz_apply_of_le a h

/--
[lowerToeplitz_apply_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
private lemma lowerToeplitz_apply_of_gt_eq
  [Zero R]
  {a : ℕ → R}
  {i j : ℕ}
-- given
  (h : i < j) :
-- imply
  lowerToeplitz a i j = 0 := by
-- proof
  apply Matrix.lowerToeplitz_apply_of_gt a h

/--
[lowerToeplitz_apply_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
private lemma lowerToeplitz_apply_diag_eq
  [Zero R]
  {a : ℕ → R}
  {i : ℕ} :
-- imply
  lowerToeplitz a i i = a 0 := by
-- proof
  apply Matrix.lowerToeplitz_apply_diag a i


-- created on 2026-10-20
