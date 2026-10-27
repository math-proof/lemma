import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
open StatMech StatMech.FrontierD


/--
[sixVertexThetaDerivativeDenominator_reflect_left_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianSign.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_reflect_left_sub_eq
  {c x y : Real} :
-- imply
  sixVertexThetaDerivativeDenominator c (-x) y - sixVertexThetaDerivativeDenominator c x y = 4 * Real.sin x * Real.sin y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_reflect_left_sub c x y

/--
[sixVertexTheta_right_difference_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianSign.lean)
-/
@[path]
private lemma sixVertexTheta_right_difference_nonneg_eq
  {c x y : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Icc (-Real.pi) 0)
  (hy : y ∈ Set.Icc (-Real.pi) 0) :
-- imply
  0 <= (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) - (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) / sixVertexThetaDerivativeDenominator c (-x) y) := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_right_difference_nonneg hc hx hy


-- created on 2026-10-23
