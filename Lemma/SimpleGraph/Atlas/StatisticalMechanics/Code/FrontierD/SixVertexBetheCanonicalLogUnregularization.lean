import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexBetheLogObservable_eq_logNormKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma sixVertexBetheLogObservable_eq_logNormKernel_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Ioo 0 Real.pi) :
-- imply
  sixVertexBetheLogObservable c x = sixVertexBetheLogNormKernel c x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogObservable_eq_logNormKernel hc hx

/--
[eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s) k let C := sixVertexCanonicalEvenOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le hc hepsilon s hM

/--
[tendsto_sixVertexLogRegularizationSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexLogRegularizationSchedule_eq :
-- imply
  Tendsto sixVertexLogRegularizationSchedule atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexLogRegularizationSchedule

/--
[sixVertexLogRegularizationSchedule_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma sixVertexLogRegularizationSchedule_pos_eq
  {m : Nat} :
-- imply
  0 < sixVertexLogRegularizationSchedule m := by
-- proof
  apply StatMech.FrontierD.sixVertexLogRegularizationSchedule_pos m

/--
[tendsto_sixVertexRegularizedLogPairing_schedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedLogPairing_schedule_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun m => ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c (sixVertexLogRegularizationSchedule m) x * sixVertexContinuousOffsetFourier c hc x) atTop (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedLogPairing_schedule hc

/--
[tendsto_sixVertexCanonicalEvenBulkLogDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenBulkLogDisplacement_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalEvenBulkLogDisplacement hc s) atTop (nhds ((2 * s : Real) / 2 * (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenBulkLogDisplacement hc s

/--
[eventually_sixVertexCanonicalFixedChargeCandidate_even_eq_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedChargeCandidate_even_eq_density_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc (2 * s) k) =ᶠ[atTop] sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedChargeCandidate_even_eq_density hc s

/--
[tendsto_sixVertexCanonicalFixedEvenDensityCandidateLogRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s) atTop (nhds (-((2 * s : Nat) : Real) * sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s

/--
[sixVertexCanonicalFixedEvenCharge_matchesOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedEvenCharge_matchesOffsetFourier_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc (2 * s) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedEvenCharge_matchesOffsetFourier hc s


-- created on 2026-10-23
