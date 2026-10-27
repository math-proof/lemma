import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
open MeasureTheory Interval StatMech StatMech.Onsager


/--
[ons_gInt_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_gInt_decompose_eq
  {beta k1 k2 : ℝ} :
-- imply
  ons_gInt beta k1 k2 = (Real.sinh (2 * beta) - 1) ^ 2 + Real.sinh (2 * beta) * (2 - Real.cos k1 - Real.cos k2) := by
-- proof
  apply StatMech.Onsager.ons_gInt_decompose beta k1 k2

/--
[ons_gInt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_gInt_betaC_eq
  {k1 k2 : ℝ} :
-- imply
  ons_gInt ons_betaC k1 k2 = 2 - Real.cos k1 - Real.cos k2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_betaC k1 k2

/--
[ons_intervalIntegrable_criticalLogBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_intervalIntegrable_criticalLogBound_eq :
-- imply
  IntervalIntegrable ons_criticalLogBound volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.Onsager.ons_intervalIntegrable_criticalLogBound

/--
[ons_criticalLogBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_criticalLogBound_nonneg_eq
  {y : ℝ} :
-- imply
  0 ≤ ons_criticalLogBound y := by
-- proof
  apply StatMech.Onsager.ons_criticalLogBound_nonneg y

/--
[ons_log_gInt_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_log_gInt_bound_eq
  {beta k1 k2 : ℝ}
-- given
  (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
  (hshi : Real.sinh (2 * beta) ≤ 2)
  (hk2 : k2 ∈ Set.Icc (-Real.pi) Real.pi)
  (hk20 : k2 ≠ 0) :
-- imply
  |Real.log (ons_gInt beta k1 k2)| ≤ ons_criticalLogBound k2 := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_bound beta k1 k2 hslo hshi hk2 hk20

/--
[ons_eventually_sinh_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_eventually_sinh_bounds_eq :
-- imply
  ∀ᶠ beta : ℝ in nhds ons_betaC, (1 / 2 : ℝ) ≤ Real.sinh (2 * beta) ∧ Real.sinh (2 * beta) ≤ 2 := by
-- proof
  apply StatMech.Onsager.ons_eventually_sinh_bounds

/--
[ons_inner_integral_tendsto_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_inner_integral_tendsto_betaC_eq
  {k1 : ℝ} :
-- imply
  Filter.Tendsto (fun beta : ℝ => ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)) (nhds ons_betaC) (nhds (∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt ons_betaC k1 k2))) := by
-- proof
  apply StatMech.Onsager.ons_inner_integral_tendsto_betaC k1

/--
[ons_inner_integral_continuous_near_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_inner_integral_continuous_near_betaC_eq
  {beta : ℝ}
-- given
  (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
  (hshi : Real.sinh (2 * beta) ≤ 2) :
-- imply
  Continuous (fun k1 : ℝ => ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)) := by
-- proof
  apply StatMech.Onsager.ons_inner_integral_continuous_near_betaC beta hslo hshi

/--
[ons_inner_integral_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_inner_integral_norm_le_eq
  {beta k1 : ℝ}
-- given
  (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
  (hshi : Real.sinh (2 * beta) ≤ 2) :
-- imply
  ‖∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)‖ ≤ ons_criticalInnerBound := by
-- proof
  apply StatMech.Onsager.ons_inner_integral_norm_le beta k1 hslo hshi

/--
[ons_double_integral_tendsto_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_double_integral_tendsto_betaC_eq :
-- imply
  Filter.Tendsto (fun beta : ℝ => ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)) (nhds ons_betaC) (nhds (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt ons_betaC k1 k2))) := by
-- proof
  apply StatMech.Onsager.ons_double_integral_tendsto_betaC

/--
[ons_continuousAt_freeEnergyIntegral_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_continuousAt_freeEnergyIntegral_betaC_eq :
-- imply
  ContinuousAt ons_freeEnergyIntegral ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_continuousAt_freeEnergyIntegral_betaC

/--
[ons_continuousAt_pressure_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean)
-/
@[path]
private lemma ons_continuousAt_pressure_betaC_eq :
-- imply
  ContinuousAt ons_pressure ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_continuousAt_pressure_betaC


-- created on 2026-10-23
