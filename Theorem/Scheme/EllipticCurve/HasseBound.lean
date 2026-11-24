module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
public import Theorem.Scheme.EllipticCurve.ManinTwist
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Lemma.Scheme.EllipticCurve.VariableChangePoint
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3


public section

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted

/--
[hasse_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/HasseBound.lean)
-/
@[path]
theorem hasse_bound
  [Field F] [Fintype F] [DecidableEq F]
  {W : WeierstrassCurve F} [W.IsElliptic] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card (W.toAffine.Point) : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26
