/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import sympy.atlas.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring

/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/

namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

/-- The affine-coordinate map associated to an admissible Weierstrass variable change. -/
def mapAffineCoordinates (C : VariableChange F) (xy : F × F) : F × F :=
  (C.u ^ 2 * xy.1 + C.r,
    C.u ^ 3 * xy.2 + C.u ^ 2 * C.s * xy.1 + C.t)

@[simp]
theorem mapAffineCoordinates_one (xy : F × F) :
    mapAffineCoordinates (1 : VariableChange F) xy = xy := by
  ext <;> simp [mapAffineCoordinates, one_def]

theorem mapAffineCoordinates_mul (C C' : VariableChange F) (xy : F × F) :
    mapAffineCoordinates (C * C') xy =
      mapAffineCoordinates C' (mapAffineCoordinates C xy) := by
  ext <;> simp only [mapAffineCoordinates, mul_def, Units.val_mul]
  · ring
  · ring

@[simp]
theorem mapAffineCoordinates_inv_apply (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C⁻¹ (mapAffineCoordinates C xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

@[simp]
theorem mapAffineCoordinates_apply_inv (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C (mapAffineCoordinates C⁻¹ xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

/-- Affine coordinates form an equivalence under an admissible Weierstrass variable change. -/
def affineCoordinatesEquiv (C : VariableChange F) : F × F ≃ F × F where
  toFun := mapAffineCoordinates C
  invFun := mapAffineCoordinates C⁻¹
  left_inv := mapAffineCoordinates_inv_apply C
  right_inv := mapAffineCoordinates_apply_inv C

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

/-- Affine solutions of Weierstrass equations are equivalent under a variable change. -/
def affineEquationEquiv (C : VariableChange F) (W : WeierstrassCurve F) :
    {xy : F × F // (C • W).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun xy :=
    ⟨mapAffineCoordinates C xy.1,
      (equation_mapAffineCoordinates_iff C W xy.1).mp xy.2⟩
  invFun xy :=
    ⟨mapAffineCoordinates C⁻¹ xy.1, by
      rw [equation_mapAffineCoordinates_iff]
      simpa using xy.2⟩
  left_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_inv_apply C xy.1
  right_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_apply_inv C xy.1

/-- Rational points of elliptic Weierstrass equations are equivalent under a variable change. -/
noncomputable def pointEquiv (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (C • W).toAffine.pointEquiv |>.trans
    ((affineEquationEquiv C W).optionCongr.trans W.toAffine.pointEquiv.symm)

/-- An admissible variable change preserves the number of rational points of an elliptic
Weierstrass equation over a finite field. -/
theorem natCard_point_eq [Finite F] (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    Nat.card ((C • W).toAffine.Point) = Nat.card W.toAffine.Point :=
  Nat.card_congr (pointEquiv C W)

end WeierstrassCurve.VariableChange
