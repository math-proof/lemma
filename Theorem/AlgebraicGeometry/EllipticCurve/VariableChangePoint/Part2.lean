/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2
/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/


namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

/-- The affine-coordinate map carries the changed Weierstrass equation to the original one. -/
theorem equation_mapAffineCoordinates_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (xy : F × F) :
    (C • W).toAffine.Equation xy.1 xy.2 ↔
      W.toAffine.Equation (mapAffineCoordinates C xy).1
        (mapAffineCoordinates C xy).2 := by
  rcases xy with ⟨x, y⟩
  change (C • W).toAffine.Equation x y ↔
    W.toAffine.Equation
      (C.u ^ 2 * x + C.r)
      (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
  rw [(C • W).toAffine.equation_iff_variableChange,
    W.toAffine.equation_iff_variableChange]
  rw [← mul_smul]
  simp only [Affine.equation_zero, variableChange_a₆]
  simp only [mul_def, one_mul, mul_zero, zero_add, Units.val_inv_eq_inv_val,
    inv_pow, mul_eq_zero, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff, Units.ne_zero, false_or, inv_one,
    Units.val_one, one_pow]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

end WeierstrassCurve.VariableChange
