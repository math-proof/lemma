import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier.Part4
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  HasDerivAt (sixVertexRegularizedBetheLogKernel c epsilon) (sixVertexRegularizedBetheLogNormDerivative c epsilon x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon

/--
[summable_sixVertexRegularizedRapidityLogDerivativeTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma summable_sixVertexRegularizedRapidityLogDerivativeTerm_eq
  {lam epsilon : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  Summable (fun n : Nat => sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexRegularizedRapidityLogDerivativeTerm hlam hepsilon alpha

/--
[hasDerivAt_sixVertexRegularizedRapidityLogSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexRegularizedRapidityLogSeries_eq
  {lam epsilon : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  HasDerivAt (fun beta => sixVertexRegularizedRapidityConstant lam epsilon + sixVertexLogCosineSeries (sixVertexRegularizedRapidityRadius lam epsilon) beta - sixVertexLogCosineSeries (sixVertexFreeEnergyRapidityRadius lam) beta) (sixVertexRegularizedRapidityLogDerivative lam epsilon alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexRegularizedRapidityLogSeries hlam hepsilon alpha

/--
[sixVertexRegularizedBetheLogDerivative_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma sixVertexRegularizedBetheLogDerivative_rapidityMomentum_eq
  {c epsilon : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  sixVertexRegularizedBetheLogNormDerivative c epsilon (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) * sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha = sixVertexRegularizedRapidityLogDerivative (sixVertexAntiferroelectricLambda c) epsilon alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedBetheLogDerivative_rapidityMomentum hc hepsilon alpha

/--
[intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset_eq
  {lam epsilon : Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : 0 < epsilon) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, sixVertexRegularizedRapidityLogDerivative lam epsilon alpha * sixVertexOffsetRapidityProfile lam alpha) = sixVertexOffsetLogFourierDampedValue lam (sixVertexRegularizedRapidityRadius lam epsilon) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset hlam hepsilon

/--
[summable_sixVertexOffsetLogFourierQTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma summable_sixVertexOffsetLogFourierQTerm_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexOffsetLogFourierQTerm lam) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexOffsetLogFourierQTerm hlam

/--
[sixVertexOffsetLogFourierQTerm_add_correction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma sixVertexOffsetLogFourierQTerm_add_correction_eq
  {lam : Real}
  {n : Nat} :
-- imply
  sixVertexOffsetLogFourierQTerm lam n + sixVertexGapCorrectionTerm lam n = -((-1 : Real) ^ (n + 1) * sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) / (n + 1 : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetLogFourierQTerm_add_correction lam n

/--
[sixVertexOffsetLogFourierQValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma sixVertexOffsetLogFourierQValue_eq_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexOffsetLogFourierQValue lam = Real.log (1 + sixVertexFreeEnergyRapidityRadius lam) - ∑' n : Nat, sixVertexGapCorrectionTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetLogFourierQValue_eq hlam

/--
[sixVertexOffsetLogFourierQValue_sub_gapSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma sixVertexOffsetLogFourierQValue_sub_gapSeries_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexOffsetLogFourierQValue lam - sixVertexGapSeries lam = Real.log (Real.cosh lam) - sixVertexAntiferroelectricGapRate lam := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetLogFourierQValue_sub_gapSeries hlam

/--
[sixVertexOffsetLogFourierDampedValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma sixVertexOffsetLogFourierDampedValue_eq_eq
  {lam : Real}
  {r : Real}
-- given
  (hlam : 0 < lam)
  (hr : r ∈ Set.Ioo 0 1) :
-- imply
  sixVertexOffsetLogFourierDampedValue lam r = sixVertexOffsetLogFourierQValue lam - r * ∑' n : Nat, sixVertexGapSeriesTerm lam n * r ^ n := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetLogFourierDampedValue_eq hlam hr

/--
[tendsto_sixVertexOffsetLogFourierDampedValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma tendsto_sixVertexOffsetLogFourierDampedValue_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (sixVertexOffsetLogFourierDampedValue lam) (nhdsWithin 1 (Set.Iio 1)) (nhds (Real.log (Real.cosh lam) - sixVertexAntiferroelectricGapRate lam)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOffsetLogFourierDampedValue hlam

/--
[tendsto_sixVertexOffsetLogFourierDampedValue_regularization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma tendsto_sixVertexOffsetLogFourierDampedValue_regularization_eq
  {lam : Real}
  {l : Filter iota}
  {epsilon : iota -> Real}
-- given
  (hlam : 0 < lam)
  (hepsilon : Tendsto epsilon l (nhds 0))
  (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i) :
-- imply
  Tendsto (fun i => sixVertexOffsetLogFourierDampedValue lam (sixVertexRegularizedRapidityRadius lam (epsilon i))) l (nhds (Real.log (Real.cosh lam) - sixVertexAntiferroelectricGapRate lam)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOffsetLogFourierDampedValue_regularization hlam hepsilon hepsilonPos

/--
[intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x) = sixVertexOffsetLogFourierDampedValue (sixVertexAntiferroelectricLambda c) (sixVertexRegularizedRapidityRadius (sixVertexAntiferroelectricLambda c) epsilon) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset hc hepsilon

/--
[continuous_sixVertexRegularizedBetheLogNormDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma continuous_sixVertexRegularizedBetheLogNormDerivative_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Continuous (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRegularizedBetheLogNormDerivative hc hepsilon

/--
[abs_mul_sixVertexRegularizedBetheLogNormDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma abs_mul_sixVertexRegularizedBetheLogNormDerivative_le_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |x * sixVertexRegularizedBetheLogNormDerivative c epsilon x| <= Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
-- proof
  apply StatMech.FrontierD.abs_mul_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon hx hxIcc

/--
[tendsto_sixVertexRegularizedBetheLogNormDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedBetheLogNormDerivative_eq
  {c x : Real}
  {l : Filter iota}
  {epsilon : iota -> Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hepsilon : Tendsto epsilon l (nhds 0)) :
-- imply
  Tendsto (fun i => sixVertexRegularizedBetheLogNormDerivative c (epsilon i) x) l (nhds (sixVertexBetheLogNormDerivative c x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedBetheLogNormDerivative hc hx hxIcc hepsilon

/--
[intervalIntegral_sixVertexBetheLogNormDerivative_mul_offset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexBetheLogNormDerivative_mul_offset_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  (∫ x in -Real.pi..Real.pi, sixVertexBetheLogNormDerivative c x * sixVertexContinuousOffsetFourier c hc x) = Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexBetheLogNormDerivative_mul_offset hc


-- created on 2026-10-23
