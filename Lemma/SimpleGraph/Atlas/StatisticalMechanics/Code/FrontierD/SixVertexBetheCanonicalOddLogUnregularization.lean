import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg hc s

/--
[sixVertexCanonicalOddMidpointHalfRoot_quantile_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma sixVertexCanonicalOddMidpointHalfRoot_quantile_lower_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.pi * (2 * (j : Real) + 1) < (sixVertexFourWidth (2 * s + 1) k : Real) * sixVertexCanonicalOddMidpointHalfRoot hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddMidpointHalfRoot_quantile_lower hc s k j

/--
[eventually_abs_sixVertexCanonicalOddPositiveRoot_sub_midpoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalOddPositiveRoot_sub_midpoint_le_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall j : Fin (s + k + 1), := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalOddPositiveRoot_sub_midpoint_le hc s

/--
[eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_simple_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s + 1) k let n := s + k + 1 let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_simple hc hepsilon s hM

/--
[eventually_abs_sixVertexCanonicalOddBulkLogDisplacement_sub_regularized_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalOddBulkLogDisplacement_sub_regularized_le_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s + 1) k let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalOddBulkLogDisplacement_sub_regularized_le hc hepsilon s hM

/--
[tendsto_sixVertexCanonicalOddRegularizedBulkLogDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddRegularizedBulkLogDisplacement_eq
  {c epsilon : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (sixVertexCanonicalOddRegularizedBulkLogDisplacement hc epsilon s) atTop (nhds ((2 * s + 1 : Real) / 2 * (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddRegularizedBulkLogDisplacement hc hepsilon s

/--
[tendsto_sixVertexCanonicalOddBulkLogDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddBulkLogDisplacement_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalOddBulkLogDisplacement hc s) atTop (nhds ((2 * s + 1 : Real) / 2 * (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddBulkLogDisplacement hc s


-- created on 2026-10-23
