import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
open StatMech StatMech.FrontierD


/--
[summable_sixVertexOffsetCorrectionLipschitzTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma summable_sixVertexOffsetCorrectionLipschitzTerm_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexOffsetCorrectionLipschitzTerm lam) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexOffsetCorrectionLipschitzTerm hlam

/--
[sixVertexOffsetCorrectionLipschitzTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma sixVertexOffsetCorrectionLipschitzTerm_nonneg_eq
  {lam : Real}
  {n : Nat} :
-- imply
  0 <= sixVertexOffsetCorrectionLipschitzTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetCorrectionLipschitzTerm_nonneg lam n

/--
[abs_sixVertexOffsetCorrectionTerm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma abs_sixVertexOffsetCorrectionTerm_sub_le_eq
  {lam : Real}
  {n : Nat}
  {alpha beta : Real} :
-- imply
  |sixVertexOffsetCorrectionTerm lam n alpha - sixVertexOffsetCorrectionTerm lam n beta| <= sixVertexOffsetCorrectionLipschitzTerm lam n * |alpha - beta| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOffsetCorrectionTerm_sub_le lam n alpha beta

/--
[sixVertexOffsetRapidityLipschitzBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma sixVertexOffsetRapidityLipschitzBound_pos_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  0 < sixVertexOffsetRapidityLipschitzBound lam := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetRapidityLipschitzBound_pos hlam

/--
[lipschitzWith_sixVertexOffsetRapidityProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexOffsetRapidityProfile_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  LipschitzWith (sixVertexOffsetRapidityLipschitzNNReal lam) (sixVertexOffsetRapidityProfile lam) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexOffsetRapidityProfile hlam

/--
[sixVertexRapidityMomentumDerivativeFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma sixVertexRapidityMomentumDerivativeFloor_pos_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  0 < sixVertexRapidityMomentumDerivativeFloor lam := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentumDerivativeFloor_pos hlam

/--
[sixVertexRapidityMomentumDerivativeFloor_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma sixVertexRapidityMomentumDerivativeFloor_le_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexRapidityMomentumDerivativeFloor lam <= sixVertexXiFourier lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentumDerivativeFloor_le hlam alpha

/--
[lipschitzWith_sixVertexMomentumRapidity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexMomentumRapidity_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  LipschitzWith (sixVertexMomentumRapidityLipschitzNNReal lam) (sixVertexMomentumRapidity lam hlam) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexMomentumRapidity hlam

/--
[lipschitzWith_sixVertexContinuousOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexContinuousOffsetFourier_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexContinuousOffsetFourierLipschitzNNReal c) (sixVertexContinuousOffsetFourier c hc) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexContinuousOffsetFourier hc


-- created on 2026-10-23
