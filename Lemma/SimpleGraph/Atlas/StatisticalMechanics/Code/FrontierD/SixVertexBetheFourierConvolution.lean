import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
open StatMech StatMech.FrontierD


/--
[norm_sixVertexXiFourierTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma norm_sixVertexXiFourierTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexXiFourierTerm lam n alpha‖ <= sixVertexFourierRootDensityMajorant lam n := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexXiFourierTerm_le lam n alpha

/--
[summable_sixVertexXiFourierTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma summable_sixVertexXiFourierTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n => sixVertexXiFourierTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexXiFourierTerm hlam alpha

/--
[continuous_sixVertexXiFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma continuous_sixVertexXiFourier_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexXiFourier lam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexXiFourier hlam

/--
[intervalIntegral_cos_succ_mul_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma intervalIntegral_cos_succ_mul_sub_eq
  {n : Nat}
  {alpha : Real} :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((n + 1 : Real) * (alpha - beta))) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cos_succ_mul_sub n alpha

/--
[intervalIntegral_shiftedCos_mul_fourierRootDensityTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma intervalIntegral_shiftedCos_mul_fourierRootDensityTerm_eq
  {lam : Real}
  {n j : Nat}
  {alpha : Real} :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((n + 1 : Real) * (alpha - beta)) * sixVertexFourierRootDensityTerm lam j beta) = if n = j then Real.pi * Real.cos ((n + 1 : Real) * alpha) / Real.cosh ((n + 1 : Real) * lam) else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_shiftedCos_mul_fourierRootDensityTerm lam n j alpha

/--
[intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((n + 1 : Real) * (alpha - beta)) * sixVertexFourierRootDensity lam beta) = Real.pi * Real.cos ((n + 1 : Real) * alpha) / Real.cosh ((n + 1 : Real) * lam) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity hlam n alpha

/--
[sixVertexFourierRootDensityNormBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma sixVertexFourierRootDensityNormBound_nonneg_eq
  {lam : Real} :
-- imply
  0 <= sixVertexFourierRootDensityNormBound lam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierRootDensityNormBound_nonneg lam

/--
[norm_sixVertexFourierRootDensity_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma norm_sixVertexFourierRootDensity_le_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  ‖sixVertexFourierRootDensity lam alpha‖ <= sixVertexFourierRootDensityNormBound lam := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexFourierRootDensity_le hlam alpha

/--
[intervalIntegral_XiFourierTerm_mul_rootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma intervalIntegral_XiFourierTerm_mul_rootDensity_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ beta in -Real.pi..Real.pi, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) * sixVertexFourierRootDensity lam beta) = sixVertexXiRootConvolutionTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_XiFourierTerm_mul_rootDensity hlam n alpha

/--
[intervalIntegral_XiFourier_mul_rootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma intervalIntegral_XiFourier_mul_rootDensity_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ beta in -Real.pi..Real.pi, sixVertexXiFourier (2 * lam) (alpha - beta) * sixVertexFourierRootDensity lam beta) = Real.pi + ∑' n : Nat, sixVertexXiRootConvolutionTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_XiFourier_mul_rootDensity hlam alpha

/--
[norm_sixVertexXiRootConvolutionTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma norm_sixVertexXiRootConvolutionTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexXiRootConvolutionTerm lam n alpha‖ <= Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexXiRootConvolutionTerm_le lam n alpha

/--
[summable_sixVertexXiRootConvolutionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma summable_sixVertexXiRootConvolutionTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n : Nat => sixVertexXiRootConvolutionTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexXiRootConvolutionTerm hlam alpha

/--
[sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  sixVertexXiFourierTerm lam n alpha - (1 / (2 * Real.pi)) * sixVertexXiRootConvolutionTerm lam n alpha = sixVertexFourierRootDensityTerm lam n alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm lam n alpha

/--
[sixVertexFourierRootDensity_integralEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean)
-/
@[path]
private lemma sixVertexFourierRootDensity_integralEquation_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexFourierRootDensity lam alpha = sixVertexXiFourier lam alpha - (1 / (2 * Real.pi)) * ∫ beta in -Real.pi..Real.pi, sixVertexXiFourier (2 * lam) (alpha - beta) * sixVertexFourierRootDensity lam beta := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierRootDensity_integralEquation hlam alpha


-- created on 2026-10-23
