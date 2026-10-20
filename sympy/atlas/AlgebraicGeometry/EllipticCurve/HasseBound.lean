/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinTwist
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
import sympy.atlas.AlgebraicGeometry.EllipticCurve.VariableChangePoint
namespace MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted

/-!
# Hasse bound for elliptic curves

Records Hasse's bound on the number of points of an elliptic curve over a finite field.
-/

/--
If `F` is a finite field and `W : WeierstrassCurve F` is elliptic, then with `q = Nat.card F` and
`N = Nat.card (W.toAffine.Point)` we have `(q + 1 - N)^2 ≤ 4 * q` in `ℤ`. Source: H. Hasse, J.
Reine Angew. Math. 1936; modern Silverman, The Arithmetic of Elliptic Curves, 2nd ed.;
Lean states integral squared form of |N-(q+1)| ≤ 2√q including point at infinity.

Proof: Manin's elementary polynomial-degree argument on a twist over `F(t)`, done separately
for the odd-characteristic and characteristic-two normal forms. In characteristic two the point
count uses the fibres of the additive map `y ↦ y² + b y`, followed by the same projective
neighboring-degree recurrence, as in Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).

Proves `Wanted` entry `hasse_bound`.
-/
theorem hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    (((Nat.card F : ℤ) + 1 - (Nat.card (W.toAffine.Point) : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  open MathlibExt.AlgebraicGeometry.EllipticCurve in
  by_cases hchar : ringChar F = 2
  · let _ : CharP F 2 := ringChar.of_eq hchar
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
    let _ : (C • W).IsCharTwoNF := hC
    have hbound := ManinTwistCharTwo.hasse_bound_of_isCharTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound
  · let _ : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hchar)
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharNeTwoNF
    let _ : (C • W).IsCharNeTwoNF := hC
    have hbound := ManinTwist.hasse_bound_of_isCharNeTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound

end MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted
