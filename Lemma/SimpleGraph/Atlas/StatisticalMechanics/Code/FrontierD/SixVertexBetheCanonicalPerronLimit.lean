import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[eventually_two_le_sixVertexPerronGaugeStage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma eventually_two_le_sixVertexPerronGaugeStage_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, 2 ≤ sixVertexPerronGaugeStage hc k := by
-- proof
  apply StatMech.FrontierD.eventually_two_le_sixVertexPerronGaugeStage hc

/--
[tendsto_sixVertexCanonicalPerronLogEpsilon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronLogEpsilon_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalPerronLogEpsilon hc) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronLogEpsilon hc

/--
[eventually_sixVertexCanonicalPerronLogEpsilon_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalPerronLogEpsilon_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, 0 < sixVertexCanonicalPerronLogEpsilon hc k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalPerronLogEpsilon_pos hc

/--
[sixVertexCanonicalPerronLogCutoff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronLogCutoff_pos_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexCanonicalPerronLogCutoff hc k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronLogCutoff_pos hc k

/--
[eventually_sixVertexCanonicalPerronLogCutoff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalPerronLogCutoff_le_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalPerronLogCutoff hc k ≤ k + 1 := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalPerronLogCutoff_le hc

/--
[tendsto_sixVertexCanonicalPerronLogCutoff_div_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronLogCutoff_div_width_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => (sixVertexCanonicalPerronLogCutoff hc k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronLogCutoff_div_width hc

/--
[tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalDensityPerronInitialLogContribution hc (sixVertexCanonicalPerronLogCutoff hc k) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule hc

/--
[tendsto_sixVertexCanonicalPerronRegularizedTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRegularizedTailBound_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalPerronLogEpsilon hc k * (sixVertexFourWidth 0 k : Real) / (4 * (sixVertexCanonicalPerronLogCutoff hc k : Real))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRegularizedTailBound hc

/--
[tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c (sixVertexCanonicalPerronLogEpsilon hc k)) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized hc

/--
[abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le_eq
  {c : Real}
  {lower : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : ∀ x : Real, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) x)
  (hepsilon : 0 < sixVertexCanonicalPerronLogEpsilon hc k) :
-- imply
  |sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c (sixVertexCanonicalPerronLogEpsilon hc k)) k - sixVertexCanonicalPerronRegularizedIntegral hc k| ≤ (sixVertexRegularizedBetheLogLipschitzConstant c (sixVertexCanonicalPerronLogEpsilon hc k) : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((sixVertexFourWidth 0 k : Real) * lower)) * (2 * Real.pi) + sixVertexCanonicalPerronRegularizedBound hc k * (sixVertexCanonicalDensityPerronGauge hc k / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le hc hlower hdensity hepsilon

/--
[sixVertexCanonicalPerronLipschitzBase_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronLipschitzBase_nonneg_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexCanonicalPerronLipschitzBase c := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronLipschitzBase_nonneg hc

/--
[coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hstage : 0 < sixVertexPerronGaugeStage hc k) :
-- imply
  (sixVertexRegularizedBetheLogLipschitzConstant c (sixVertexCanonicalPerronLogEpsilon hc k) : Real) = sixVertexCanonicalPerronLipschitzBase c + (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
-- proof
  apply StatMech.FrontierD.coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule hc hstage

/--
[abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hstage : 2 ≤ sixVertexPerronGaugeStage hc k) :
-- imply
  |sixVertexRegularizedBetheLogKernel c (sixVertexCanonicalPerronLogEpsilon hc k) 0| ≤ (1 / 2 : Real) * |Real.log (c ^ 4)| + 2 * (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule hc hstage

/--
[eventually_sixVertexCanonicalPerronLipschitz_div_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalPerronLipschitz_div_width_le_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, (sixVertexRegularizedBetheLogLipschitzConstant c (sixVertexCanonicalPerronLogEpsilon hc k) : Real) / (sixVertexFourWidth 0 k : Real) ≤ (sixVertexCanonicalPerronLipschitzBase c + 1) / (sixVertexPerronGaugeStage hc k : Real) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalPerronLipschitz_div_width_le hc

/--
[tendsto_sixVertexCanonicalPerronLipschitz_div_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronLipschitz_div_width_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => (sixVertexRegularizedBetheLogLipschitzConstant c (sixVertexCanonicalPerronLogEpsilon hc k) : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronLipschitz_div_width hc

/--
[tendsto_sixVertexCanonicalPerronQuadratureError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronQuadratureError_eq
  {c : Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun k => (sixVertexRegularizedBetheLogLipschitzConstant c (sixVertexCanonicalPerronLogEpsilon hc k) : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((sixVertexFourWidth 0 k : Real) * lower)) * (2 * Real.pi)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronQuadratureError hc hlower

/--
[sixVertexCanonicalPerronDensityBoundConstant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronDensityBoundConstant_nonneg_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexCanonicalPerronDensityBoundConstant c := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronDensityBoundConstant_nonneg hc

/--
[eventually_sixVertexCanonicalPerronBound_mul_gauge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalPerronBound_mul_gauge_le_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalPerronRegularizedBound hc k * sixVertexCanonicalDensityPerronGauge hc k ≤ sixVertexCanonicalPerronDensityBoundConstant c / (sixVertexPerronGaugeStage hc k : Real) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalPerronBound_mul_gauge_le hc

/--
[tendsto_sixVertexCanonicalPerronBound_mul_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronBound_mul_gauge_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalPerronRegularizedBound hc k * sixVertexCanonicalDensityPerronGauge hc k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronBound_mul_gauge hc

/--
[tendsto_sixVertexCanonicalPerronDensityError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronDensityError_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalPerronRegularizedBound hc k * (sixVertexCanonicalDensityPerronGauge hc k / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) * (2 * Real.pi)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronDensityError hc

/--
[tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c (sixVertexCanonicalPerronLogEpsilon hc k)) k - sixVertexCanonicalPerronRegularizedIntegral hc k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral hc

/--
[tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalPerronRegularizedIntegral hc k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral hc


-- created on 2026-10-23
