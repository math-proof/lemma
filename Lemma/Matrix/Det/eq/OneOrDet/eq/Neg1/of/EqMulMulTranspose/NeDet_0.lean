import Mathlib
import sympy.Basic
open Matrix


namespace Garrett

/--
[isometry_det_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsometryDet.lean)
-/
@[path]
lemma isometry_det_eq_one_or_neg_one
  [DecidableEq n]
  [Fintype n]
  [CommRing R]
  [NoZeroDivisors R]
  {Q g : Matrix n n R}
-- given
  (hQ : Q.det ≠ 0)
  (hiso : g.transpose * Q * g = Q) :
-- imply
  g.det = 1 ∨ g.det = -1 := by
-- proof
  have h1 : (g.transpose * Q * g).det = Q.det := by rw [hiso]
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : g.det ^ 2 * Q.det = Q.det := by
    have : g.det * Q.det * g.det = g.det ^ 2 * Q.det := by ring
    rw [← this]; exact h1
  have h3 : (g.det ^ 2 - 1) * Q.det = 0 := by
    have : (g.det ^ 2 - 1) * Q.det = g.det ^ 2 * Q.det - Q.det := by ring
    rw [this, h2, sub_self]
  have h4 : g.det ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_right hQ
  have h5 : g.det ^ 2 = 1 := by
    have : g.det ^ 2 = g.det ^ 2 - 1 + 1 := by ring
    rw [this, h4, zero_add]
  exact sq_eq_one_iff.mp h5

end Garrett

namespace Garrett

/--
[isometry_det_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsometryDet.lean)
-/
@[path]
lemma isometry_det_sq_eq_one
  [DecidableEq n]
  [Fintype n]
  [CommRing R]
  [NoZeroDivisors R]
  {Q g : Matrix n n R}
-- given
  (hQ : Q.det ≠ 0)
  (hiso : g.transpose * Q * g = Q) :
-- imply
  g.det ^ 2 = 1 := by
-- proof
  obtain h | h <;> simp [h] := isometry_det_eq_one_or_neg_one hQ hiso

end Garrett


-- created on 2026-10-23
