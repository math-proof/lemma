import Mathlib
import sympy.Basic
import Def.LinearAlgebra.Matrix.LowerToeplitz
open Matrix


namespace Matrix

/--
[lowerToeplitz_apply_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
lemma lowerToeplitz_apply_of_le
  [Zero R]
  {a : ℕ → R}
  {i j : ℕ}
-- given
  (h : j ≤ i) :
-- imply
  lowerToeplitz a i j = a (i - j) := by
-- proof
  simp [lowerToeplitz, h]

end Matrix

namespace Matrix

/--
[lowerToeplitz_apply_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
lemma lowerToeplitz_apply_of_gt
  [Zero R]
  {a : ℕ → R}
  {i j : ℕ}
-- given
  (h : i < j) :
-- imply
  lowerToeplitz a i j = 0 := by
-- proof
  simp [lowerToeplitz, Nat.not_le.mpr h]

end Matrix

namespace Matrix

/--
[lowerToeplitz_apply_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean)
-/
@[path]
lemma lowerToeplitz_apply_diag
  [Zero R]
  {a : ℕ → R}
  {i : ℕ} :
-- imply
  lowerToeplitz a i i = a 0 := by
-- proof
  have h : i ≤ i := Nat.le_refl i
  rw [lowerToeplitz_apply_of_le a h, Nat.sub_self]

end Matrix


-- created on 2026-10-20
-- updated on 2026-10-23
