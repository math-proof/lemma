import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier
open StatMech StatMech.FrontierD


/--
[norm_sixVertexOffsetCorrectionTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma norm_sixVertexOffsetCorrectionTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real} :
-- imply
  ‖sixVertexOffsetCorrectionTerm lam n alpha‖ <= (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexOffsetCorrectionTerm_le lam n alpha

/--
[summable_sixVertexOffsetCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma summable_sixVertexOffsetCorrectionTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n => sixVertexOffsetCorrectionTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexOffsetCorrectionTerm hlam alpha

/--
[continuous_sixVertexOffsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma continuous_sixVertexOffsetRapidityProfile_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexOffsetRapidityProfile lam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexOffsetRapidityProfile hlam

/--
[odd_sixVertexOffsetCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma odd_sixVertexOffsetCorrectionTerm_eq
  {lam : Real}
  {n : Nat} :
-- imply
  Function.Odd (sixVertexOffsetCorrectionTerm lam n) := by
-- proof
  apply StatMech.FrontierD.odd_sixVertexOffsetCorrectionTerm lam n

/--
[odd_sixVertexOffsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma odd_sixVertexOffsetRapidityProfile_eq
  {lam : Real} :
-- imply
  Function.Odd (sixVertexOffsetRapidityProfile lam) := by
-- proof
  apply StatMech.FrontierD.odd_sixVertexOffsetRapidityProfile lam

/--
[continuous_sixVertexContinuousOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma continuous_sixVertexContinuousOffsetFourier_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexContinuousOffsetFourier c hc) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexContinuousOffsetFourier hc

/--
[sixVertexContinuousOffsetFourier_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetFourier_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexContinuousOffsetFourier c hc (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = sixVertexOffsetRapidityProfile (sixVertexAntiferroelectricLambda c) alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetFourier_rapidityMomentum hc halpha

/--
[sixVertexRapidityMomentum_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma sixVertexRapidityMomentum_neg_eq
  {lam alpha : Real} :
-- imply
  sixVertexRapidityMomentum lam (-alpha) = -sixVertexRapidityMomentum lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentum_neg lam alpha

/--
[sixVertexMomentumRapidity_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma sixVertexMomentumRapidity_neg_eq
  {lam : Real}
  {x : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexMomentumRapidity lam hlam (-x) = -sixVertexMomentumRapidity lam hlam x := by
-- proof
  apply StatMech.FrontierD.sixVertexMomentumRapidity_neg hlam x

/--
[odd_sixVertexContinuousOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma odd_sixVertexContinuousOffsetFourier_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Function.Odd (sixVertexContinuousOffsetFourier c hc) := by
-- proof
  apply StatMech.FrontierD.odd_sixVertexContinuousOffsetFourier hc

/--
[intervalIntegral_sin_nat_mul_mul_sin_nat_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma intervalIntegral_sin_nat_mul_mul_sin_nat_mul_eq
  {m n : Nat}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, Real.sin ((m : Real) * alpha) * Real.sin ((n : Real) * alpha)) = if m = n then Real.pi else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sin_nat_mul_mul_sin_nat_mul hm hn

/--
[intervalIntegral_linearOffset_mul_sin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma intervalIntegral_linearOffset_mul_sin_eq
  {m : Nat}
-- given
  (hm : 0 < m) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha)) = (-1 : Real) ^ m / (m : Real) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_linearOffset_mul_sin hm

/--
[intervalIntegral_offsetCorrectionTerm_mul_sin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma intervalIntegral_offsetCorrectionTerm_mul_sin_eq
  {lam : Real}
  {n : Nat}
  {m : Nat}
-- given
  (hm : 0 < m) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, sixVertexOffsetCorrectionTerm lam n alpha * Real.sin ((m : Real) * alpha)) = if n + 1 = m then sixVertexGapCorrectionTerm lam n else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_offsetCorrectionTerm_mul_sin lam n hm

/--
[intervalIntegral_offsetCorrection_mul_sin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma intervalIntegral_offsetCorrection_mul_sin_eq
  {lam : Real}
  {m : Nat}
-- given
  (hlam : 0 < lam)
  (hm : 0 < m) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) * Real.sin ((m : Real) * alpha)) = sixVertexGapCorrectionTerm lam (m - 1) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_offsetCorrection_mul_sin hlam hm

/--
[sixVertexOffsetRapidityProfile_sineCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean)
-/
@[path]
private lemma sixVertexOffsetRapidityProfile_sineCoefficient_eq
  {lam : Real}
  {m : Nat}
-- given
  (hlam : 0 < lam)
  (hm : 0 < m) :
-- imply
  (1 / Real.pi) * (∫ alpha in -Real.pi..Real.pi, sixVertexOffsetRapidityProfile lam alpha * Real.sin ((m : Real) * alpha)) = (-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (Real.pi * (m : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetRapidityProfile_sineCoefficient hlam hm


-- created on 2026-10-23
