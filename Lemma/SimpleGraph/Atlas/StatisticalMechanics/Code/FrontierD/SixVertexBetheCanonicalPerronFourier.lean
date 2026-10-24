import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[hasSum_sixVertexLogCosineSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma hasSum_sixVertexLogCosineSeries_eq
  {r : Real}
  {alpha : Real}
-- given
  (hr : |r| < 1) :
-- imply
  HasSum (fun n : Nat => r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) / (n + 1 : Real)) (-Real.log ‖(1 : Complex) - (r : Complex) * Complex.exp (Complex.I * alpha)‖) := by
-- proof
  apply StatMech.FrontierD.hasSum_sixVertexLogCosineSeries hr alpha

/--
[sixVertexLogCosineSeries_eq_neg_log_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexLogCosineSeries_eq_neg_log_norm_eq
  {r : Real}
  {alpha : Real}
-- given
  (hr : |r| < 1) :
-- imply
  sixVertexLogCosineSeries r alpha = -Real.log ‖(1 : Complex) - (r : Complex) * Complex.exp (Complex.I * alpha)‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexLogCosineSeries_eq_neg_log_norm hr alpha

/--
[one_lt_sixVertexRegularizedRapidityDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma one_lt_sixVertexRegularizedRapidityDelta_eq
  {lam epsilon : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  1 < sixVertexRegularizedRapidityDelta lam epsilon := by
-- proof
  apply StatMech.FrontierD.one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon

/--
[sixVertexRegularizedRapidityRadius_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexRegularizedRapidityRadius_mem_Ioo_eq
  {lam epsilon : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  sixVertexRegularizedRapidityRadius lam epsilon ∈ Set.Ioo 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon

/--
[sixVertexRegularizedRapidityDelta_eq_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexRegularizedRapidityDelta_eq_radius_eq
  {lam epsilon : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  sixVertexRegularizedRapidityDelta lam epsilon = (sixVertexRegularizedRapidityRadius lam epsilon + (sixVertexRegularizedRapidityRadius lam epsilon)⁻¹) / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedRapidityDelta_eq_radius hlam hepsilon

/--
[intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity_eq
  {c : Real}
  {f : Real → Real}
-- given
  (hc : 2 < c)
  (hf : Continuous f) :
-- imply
  (∫ x in -Real.pi..Real.pi, f x * sixVertexFourierPhysicalDensity c hc x) = (1 / (2 * Real.pi)) * ∫ alpha in -Real.pi..Real.pi, f (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) * sixVertexFourierRootDensity (sixVertexAntiferroelectricLambda c) alpha := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity hc hf

/--
[sixVertexBetheLogNumerator_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexBetheLogNumerator_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheLogNumerator c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = 2 * (Real.cosh (sixVertexAntiferroelectricLambda c) + 1) * (Real.cosh (2 * sixVertexAntiferroelectricLambda c) - Real.cos alpha) / (Real.cosh (sixVertexAntiferroelectricLambda c) - Real.cos alpha) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogNumerator_rapidityMomentum hc alpha

/--
[sixVertexBetheLogDenominator_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexBetheLogDenominator_rapidityMomentum_eq
  {c epsilon : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  sixVertexBetheLogDenominator (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) + epsilon = sixVertexRegularizedRapidityB (sixVertexAntiferroelectricLambda c) epsilon * (sixVertexRegularizedRapidityDelta (sixVertexAntiferroelectricLambda c) epsilon - Real.cos alpha) / (Real.cosh (sixVertexAntiferroelectricLambda c) - Real.cos alpha) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogDenominator_rapidityMomentum hc hepsilon alpha

/--
[intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity_eq
  {lam r : Real}
-- given
  (hlam : 0 < lam)
  (hr : |r| < 1) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, sixVertexLogCosineSeries r alpha * sixVertexFourierRootDensity lam alpha) = ∑' n : Nat, Real.pi * r ^ (n + 1) / ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam)) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity hlam hr

/--
[sixVertexFreeEnergyRapidityRadius_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexFreeEnergyRapidityRadius_mem_Ioo_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexFreeEnergyRapidityRadius lam ∈ Set.Ioo 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam

/--
[cosh_two_eq_sixVertexFreeEnergyRapidityRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma cosh_two_eq_sixVertexFreeEnergyRapidityRadius_eq
  {lam : Real} :
-- imply
  Real.cosh (2 * lam) = (sixVertexFreeEnergyRapidityRadius lam + (sixVertexFreeEnergyRapidityRadius lam)⁻¹) / 2 := by
-- proof
  apply StatMech.FrontierD.cosh_two_eq_sixVertexFreeEnergyRapidityRadius lam

/--
[sq_norm_one_sub_radius_exp_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sq_norm_one_sub_radius_exp_mul_I_eq
  {r alpha : Real} :
-- imply
  ‖(1 : Complex) - (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 = 1 - 2 * r * Real.cos alpha + r ^ 2 := by
-- proof
  apply StatMech.FrontierD.sq_norm_one_sub_radius_exp_mul_I r alpha

/--
[log_radius_add_inv_div_two_sub_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma log_radius_add_inv_div_two_sub_cos_eq
  {r : Real}
  {alpha : Real}
-- given
  (hr : r ∈ Set.Ioo 0 1) :
-- imply
  Real.log ((r + r⁻¹) / 2 - Real.cos alpha) = 2 * Real.log ‖(1 : Complex) - (r : Complex) * Complex.exp (Complex.I * alpha)‖ - Real.log (2 * r) := by
-- proof
  apply StatMech.FrontierD.log_radius_add_inv_div_two_sub_cos hr alpha

/--
[sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series_eq
  {c epsilon : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  sixVertexRegularizedBetheLogKernel c epsilon (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = sixVertexRegularizedRapidityConstant (sixVertexAntiferroelectricLambda c) epsilon + sixVertexLogCosineSeries (sixVertexRegularizedRapidityRadius (sixVertexAntiferroelectricLambda c) epsilon) alpha - sixVertexLogCosineSeries (sixVertexFreeEnergyRapidityRadius (sixVertexAntiferroelectricLambda c)) alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series hc hepsilon alpha

/--
[summable_sixVertexAbelRootDensitySeriesTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma summable_sixVertexAbelRootDensitySeriesTerm_eq
  {lam r : Real}
-- given
  (hr : |r| < 1) :
-- imply
  Summable (sixVertexAbelRootDensitySeriesTerm lam r) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexAbelRootDensitySeriesTerm hr

/--
[sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  (∫ y in -Real.pi..Real.pi, sixVertexRegularizedBetheLogKernel c epsilon y * sixVertexFourierPhysicalDensity c hc y) = sixVertexRegularizedRapidityFourierValue (sixVertexAntiferroelectricLambda c) epsilon := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue hc hepsilon


-- created on 2026-10-23
