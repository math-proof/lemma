import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.FKReparameterization


/--
[pOfBeta_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBeta_strictMono_eq :
-- imply
  StrictMono IsingFK.pOfBeta := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBeta_strictMono

/--
[hasDerivAt_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma hasDerivAt_pOfBeta_eq
  {β : ℝ} :
-- imply
  HasDerivAt IsingFK.pOfBeta (2 * Real.exp (-2 * β)) β := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.hasDerivAt_pOfBeta β

/--
[pOfBetaDistancePrefactor_eq_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBetaDistancePrefactor_eq_slope_eq
  {βc β : ℝ}
-- given
  (hβ : β ≠ βc) :
-- imply
  pOfBetaDistancePrefactor βc β = slope IsingFK.pOfBeta βc β := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBetaDistancePrefactor_eq_slope hβ

/--
[pOfBetaDistancePrefactor_pos_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBetaDistancePrefactor_pos_of_lt_eq
  {βc β : ℝ}
-- given
  (hβ : β < βc) :
-- imply
  0 < pOfBetaDistancePrefactor βc β := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBetaDistancePrefactor_pos_of_lt hβ

/--
[pOfBeta_criticalDistance_eq_prefactor_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBeta_criticalDistance_eq_prefactor_mul_eq
  {βc β : ℝ}
-- given
  (hβ : β ≠ βc) :
-- imply
  IsingFK.pOfBeta βc - IsingFK.pOfBeta β = pOfBetaDistancePrefactor βc β * (βc - β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBeta_criticalDistance_eq_prefactor_mul hβ

/--
[tendsto_pOfBetaDistancePrefactor_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma tendsto_pOfBetaDistancePrefactor_left_eq
  {βc : ℝ} :
-- imply
  Filter.Tendsto (pOfBetaDistancePrefactor βc) (nhdsWithin βc (Set.Iio βc)) (nhds (2 * Real.exp (-2 * βc))) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.tendsto_pOfBetaDistancePrefactor_left βc

/--
[tendsto_log_pOfBetaDistancePrefactor_div_log_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma tendsto_log_pOfBetaDistancePrefactor_div_log_left_eq
  {βc : ℝ} :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (pOfBetaDistancePrefactor βc β) / Real.log (βc - β)) (nhdsWithin βc (Set.Iio βc)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.tendsto_log_pOfBetaDistancePrefactor_div_log_left βc

/--
[eventually_pOfBetaDistancePrefactor_mem_Ioo_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma eventually_pOfBetaDistancePrefactor_mem_Ioo_left_eq
  {βc : ℝ} :
-- imply
  ∀ᶠ β in nhdsWithin βc (Set.Iio βc), pOfBetaDistancePrefactor βc β ∈ Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc)) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.eventually_pOfBetaDistancePrefactor_mem_Ioo_left βc

/--
[eventually_pOfBeta_criticalDistance_comparable_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma eventually_pOfBeta_criticalDistance_comparable_left_eq
  {βc : ℝ} :
-- imply
  ∀ᶠ β in nhdsWithin βc (Set.Iio βc), Real.exp (-2 * βc) * (βc - β) ≤ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤ (3 * Real.exp (-2 * βc)) * (βc - β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.eventually_pOfBeta_criticalDistance_comparable_left βc

/--
[exists_Ioo_subset_of_eventually_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exists_Ioo_subset_of_eventually_left_eq
  {βc : ℝ}
  {P : ℝ → Prop}
-- given
  (hP : ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P β) :
-- imply
  ∃ δ, 0 < δ ∧ ∀ β, β ∈ Set.Ioo (βc - δ) βc → P β := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exists_Ioo_subset_of_eventually_left hP

/--
[exists_pOfBeta_criticalDistance_comparable_Ioo_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exists_pOfBeta_criticalDistance_comparable_Ioo_left_eq
  {βc : ℝ} :
-- imply
  ∃ δ, 0 < δ ∧ ∀ β, β ∈ Set.Ioo (βc - δ) βc → Real.exp (-2 * βc) * (βc - β) ≤ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤ (3 * Real.exp (-2 * βc)) * (βc - β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exists_pOfBeta_criticalDistance_comparable_Ioo_left βc

/--
[pOfBetaCriticalDistanceComparableWindow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBetaCriticalDistanceComparableWindow_pos_eq
  {βc : ℝ} :
-- imply
  0 < pOfBetaCriticalDistanceComparableWindow βc := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBetaCriticalDistanceComparableWindow_pos βc

/--
[pOfBeta_criticalDistance_comparable_of_mem_Ioo_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBeta_criticalDistance_comparable_of_mem_Ioo_left_eq
  {βc β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (βc - pOfBetaCriticalDistanceComparableWindow βc) βc) :
-- imply
  Real.exp (-2 * βc) * (βc - β) ≤ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧ IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤ (3 * Real.exp (-2 * βc)) * (βc - β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBeta_criticalDistance_comparable_of_mem_Ioo_left hβ

/--
[exp_log_lower_power_transfer_of_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exp_log_lower_power_transfer_of_mul_le_eq
  {lo d p k δ : ℝ}
-- given
  (hlo : 0 < lo)
  (hd : 0 < d)
  (hdlt : d < 1)
  (hk : 0 ≤ k)
  (hδ : 0 ≤ δ)
  (hcomp : lo * d ≤ p) :
-- imply
  Real.exp (k * Real.log lo) * Real.exp ((k + δ) * Real.log d) ≤ Real.exp (k * Real.log p) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exp_log_lower_power_transfer_of_mul_le hlo hd hdlt hk hδ hcomp

/--
[exp_log_lower_power_transfer_no_slack_of_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exp_log_lower_power_transfer_no_slack_of_mul_le_eq
  {lo d p k : ℝ}
-- given
  (hlo : 0 < lo)
  (hd : 0 < d)
  (hk : 0 ≤ k)
  (hcomp : lo * d ≤ p) :
-- imply
  Real.exp (k * Real.log lo) * Real.exp (k * Real.log d) ≤ Real.exp (k * Real.log p) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exp_log_lower_power_transfer_no_slack_of_mul_le hlo hd hk hcomp

/--
[exp_log_power_slack_le_of_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exp_log_power_slack_le_of_lt_one_eq
  {d k δ : ℝ}
-- given
  (hd : 0 < d)
  (hdlt : d < 1)
  (hδ : 0 ≤ δ) :
-- imply
  Real.exp ((k + δ) * Real.log d) ≤ Real.exp (k * Real.log d) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exp_log_power_slack_le_of_lt_one hd hdlt hδ

/--
[expLogUpperComparisonPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma expLogUpperComparisonPrefactor_pos_eq
-- given
  (lo hi k : ℝ) :
-- imply
  0 < expLogUpperComparisonPrefactor lo hi k := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.expLogUpperComparisonPrefactor_pos lo hi k

/--
[exp_log_upper_power_transfer_of_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exp_log_upper_power_transfer_of_comparable_eq
  {lo hi d p k : ℝ}
-- given
  (hlo : 0 < lo)
  (hhi : 0 < hi)
  (hd : 0 < d)
  (hlo_comp : lo * d ≤ p)
  (hhi_comp : p ≤ hi * d) :
-- imply
  Real.exp (k * Real.log p) ≤ expLogUpperComparisonPrefactor lo hi k * Real.exp (k * Real.log d) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exp_log_upper_power_transfer_of_comparable hlo hhi hd hlo_comp hhi_comp

/--
[pOfBeta_leftCriticalReparam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBeta_leftCriticalReparam_eq
  {βc : ℝ} :
-- imply
  LeftCriticalReparam (ParameterModel βc) (ParameterModel (IsingFK.pOfBeta βc)) IsingFK.pOfBeta where tendsto_left := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBeta_leftCriticalReparam βc

/--
[eventually_pOfBeta_mem_Ioo_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma eventually_pOfBeta_mem_Ioo_left_eq
  {βc pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∀ᶠ β in nhdsWithin βc (Set.Iio βc), IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.eventually_pOfBeta_mem_Ioo_left hpδ

/--
[exists_pOfBeta_mem_Ioo_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma exists_pOfBeta_mem_Ioo_left_eq
  {βc pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∃ δ, 0 < δ ∧ ∀ β, β ∈ Set.Ioo (βc - δ) βc → IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.exists_pOfBeta_mem_Ioo_left hpδ

/--
[pOfBetaLeftPullbackWindow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBetaLeftPullbackWindow_pos_eq
  {βc : ℝ}
  {pWindow : ℝ → ℝ}
  {ε : ℝ}
-- given
  (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
  (hε : 0 < ε) :
-- imply
  0 < pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBetaLeftPullbackWindow_pos βc pWindow pWindow_pos hε

/--
[pOfBeta_mem_Ioo_of_mem_leftPullbackWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma pOfBeta_mem_Ioo_of_mem_leftPullbackWindow_eq
  {βc : ℝ}
  {pWindow : ℝ → ℝ}
  {ε β : ℝ}
-- given
  (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
  (hε : 0 < ε)
  (hβ : β ∈ Set.Ioo (βc - pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε) βc) :
-- imply
  IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta βc - pWindow ε) (IsingFK.pOfBeta βc) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow βc pWindow pWindow_pos hε hβ

/--
[hasCriticalNu_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_comp_pOfBeta_eq
  {correlationLength : ℝ → ℝ}
  {βc ν : ℝ}
-- given
  (hν : HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc)) correlationLength ν) :
-- imply
  HasCriticalNu (ParameterModel βc) (fun β => correlationLength (IsingFK.pOfBeta β)) ν := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.hasCriticalNu_comp_pOfBeta hν

/--
[eventually_comp_pOfBeta_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma eventually_comp_pOfBeta_left_eq
  {βc : ℝ}
  {P : ℝ → Prop}
-- given
  (hP : ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc) (Set.Iio (IsingFK.pOfBeta βc)), P p) :
-- imply
  ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.eventually_comp_pOfBeta_left hP

/--
[eventually_eq_comp_pOfBeta_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma eventually_eq_comp_pOfBeta_left_eq
  {βc : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hEq : ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc) (Set.Iio (IsingFK.pOfBeta βc)), f p = g p) :
-- imply
  ∀ᶠ β in nhdsWithin βc (Set.Iio βc), f (IsingFK.pOfBeta β) = g (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.eventually_eq_comp_pOfBeta_left hEq

/--
[hasCriticalNu_comp_pOfBeta_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_comp_pOfBeta_congr_eventually_eq
  {βc ν : ℝ}
  {fkCorrelationLength comparisonLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc)) fkCorrelationLength ν)
  (hEq : ∀ᶠ β in nhdsWithin βc (Set.Iio βc), comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu (ParameterModel βc) comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.FKReparameterization.hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq


-- created on 2026-10-23
