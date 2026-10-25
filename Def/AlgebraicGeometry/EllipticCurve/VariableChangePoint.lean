/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
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

end WeierstrassCurve.VariableChange
