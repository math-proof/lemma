import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
open StatMech StatMech.FrontierD


/--
[norm_sixVertexOffsetSourceCorrectionTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma norm_sixVertexOffsetSourceCorrectionTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexOffsetSourceCorrectionTerm lam n alpha‖ <= 2 * Real.exp (-2 * lam) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexOffsetSourceCorrectionTerm_le lam n alpha

/--
[summable_sixVertexOffsetSourceCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma summable_sixVertexOffsetSourceCorrectionTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n => sixVertexOffsetSourceCorrectionTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexOffsetSourceCorrectionTerm hlam alpha

/--
[continuous_sixVertexOffsetSourceRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma continuous_sixVertexOffsetSourceRapidityProfile_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexOffsetSourceRapidityProfile lam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexOffsetSourceRapidityProfile hlam

/--
[hasDerivAt_sixVertexOffsetSourceCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexOffsetSourceCorrectionTerm_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  HasDerivAt (sixVertexOffsetSourceCorrectionTerm lam n) (sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexOffsetSourceCorrectionTerm lam n alpha

/--
[norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha‖ <= sixVertexFourierRootDensityMajorant (2 * lam) n := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le lam n alpha

/--
[hasDerivAt_sixVertexOffsetSourceRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  HasDerivAt (sixVertexOffsetSourceRapidityProfile lam) (-1 + ∑' n : Nat, sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexOffsetSourceRapidityProfile hlam alpha

/--
[sixVertexOffsetSourceCorrectionDerivativeTerm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexOffsetSourceCorrectionDerivativeTerm_eq_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha = -sixVertexXiFourierTerm (2 * lam) n (alpha - Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetSourceCorrectionDerivativeTerm_eq lam n alpha

/--
[sixVertexXiFourier_add_pi_eq_sub_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexXiFourier_add_pi_eq_sub_pi_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexXiFourier lam (alpha + Real.pi) = sixVertexXiFourier lam (alpha - Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexXiFourier_add_pi_eq_sub_pi hlam alpha

/--
[hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  HasDerivAt (sixVertexOffsetSourceRapidityProfile lam) (-sixVertexXiFourier (2 * lam) (alpha - Real.pi)) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi hlam alpha

/--
[hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun t => sixVertexContinuousOffsetSource c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) t)) (-(sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c) (alpha + Real.pi) + sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c) (alpha - Real.pi)) / 2) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum hc alpha

/--
[hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun t => sixVertexContinuousOffsetSource c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) t)) (-sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c) (alpha - Real.pi)) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi hc alpha

/--
[sixVertexContinuousOffsetSource_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetSource_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexContinuousOffsetSource c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = sixVertexOffsetSourceRapidityProfile (sixVertexAntiferroelectricLambda c) alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetSource_rapidityMomentum hc alpha

/--
[norm_sixVertexOffsetConvolutionTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma norm_sixVertexOffsetConvolutionTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexOffsetConvolutionTerm lam n alpha‖ <= 2 * Real.exp (-2 * lam) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexOffsetConvolutionTerm_le lam n alpha

/--
[summable_sixVertexOffsetConvolutionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma summable_sixVertexOffsetConvolutionTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n => sixVertexOffsetConvolutionTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexOffsetConvolutionTerm hlam alpha

/--
[intervalIntegral_shiftedCos_mul_offsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma intervalIntegral_shiftedCos_mul_offsetRapidityProfile_eq
  {lam : Real}
  {m : Nat}
  {alpha : Real}
-- given
  (hlam : 0 < lam)
  (hm : 0 < m) :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((m : Real) * (alpha - beta)) * sixVertexOffsetRapidityProfile lam beta) = Real.sin ((m : Real) * alpha) * ((-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (m : Real)) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_shiftedCos_mul_offsetRapidityProfile hlam hm alpha

/--
[intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ beta in -Real.pi..Real.pi, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) * sixVertexOffsetRapidityProfile lam beta) = sixVertexOffsetConvolutionTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile hlam n alpha

/--
[intervalIntegral_XiFourier_mul_offsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma intervalIntegral_XiFourier_mul_offsetRapidityProfile_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ beta in -Real.pi..Real.pi, sixVertexXiFourier (2 * lam) (alpha - beta) * sixVertexOffsetRapidityProfile lam beta) = ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_XiFourier_mul_offsetRapidityProfile hlam alpha

/--
[exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh_eq
  {x : Real} :
-- imply
  Real.exp (-2 * x) * (1 + Real.tanh x) = 1 - Real.tanh x := by
-- proof
  apply StatMech.FrontierD.exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh x

/--
[sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  sixVertexOffsetSourceCorrectionTerm lam n alpha - sixVertexOffsetConvolutionTerm lam n alpha = 2 * Real.pi * sixVertexOffsetCorrectionTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm lam n alpha

/--
[sixVertexOffsetRapidityProfile_integralEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexOffsetRapidityProfile_integralEquation_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  2 * Real.pi * sixVertexOffsetRapidityProfile lam alpha = sixVertexOffsetSourceRapidityProfile lam alpha - ∫ beta in -Real.pi..Real.pi, sixVertexXiFourier (2 * lam) (alpha - beta) * sixVertexOffsetRapidityProfile lam beta := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetRapidityProfile_integralEquation hlam alpha

/--
[intervalIntegral_continuousOffsetKernel_mul_fourier_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma intervalIntegral_continuousOffsetKernel_mul_fourier_pullback_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  (∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) y * sixVertexContinuousOffsetFourier c hc y) = ∫ beta in -Real.pi..Real.pi, sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c) (alpha - beta) * sixVertexOffsetRapidityProfile (sixVertexAntiferroelectricLambda c) beta := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_continuousOffsetKernel_mul_fourier_pullback hc alpha

/--
[sixVertexContinuousOffsetFourier_satisfiesEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetFourier_satisfiesEquation_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesContinuousOffsetEquation c (sixVertexContinuousOffsetFourier c hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetFourier_satisfiesEquation hc


-- created on 2026-10-23
