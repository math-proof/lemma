/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring
import Theorem.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2
/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/


namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

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

end WeierstrassCurve.VariableChange
