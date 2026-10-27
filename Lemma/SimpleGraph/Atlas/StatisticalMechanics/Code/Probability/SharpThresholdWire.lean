import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.SharpThresholdWire.Part2
open Finset Real Set StatMech StatMech.OSSS StatMech.Probability


/--
[stw_master_q_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_master_q_value_eq
  {u : ℝ}
  {ρ : ℝ}
-- given
  (hρsq : ρ ^ 2 = 1 - u) :
-- imply
  (1 + ρ ^ 2 : ℝ) = 2 - u := by
-- proof
  apply StatMech.Probability.stw_master_q_value ρ hρsq

/--
[stw_master_uses_exponent_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_master_uses_exponent_le_two_eq
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  1 < 2 - u ∧ 2 - u ≤ 2 := by
-- proof
  apply StatMech.Probability.stw_master_uses_exponent_le_two hu0 hu1

/--
[stw_ranges_meet_only_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_ranges_meet_only_at_two_eq
  {q : ℝ}
-- given
  (hfwd : 2 ≤ q ∧ q ≤ 4)
  (hmaster : 1 < q ∧ q ≤ 2) :
-- imply
  q = 2 := by
-- proof
  apply StatMech.Probability.stw_ranges_meet_only_at_two hfwd hmaster

/--
[stw_variance_coeff_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_variance_coeff_gap_eq
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  4 * p ^ 2 * (1 - p) ^ 2 ≤ p * (1 - p) := by
-- proof
  apply StatMech.Probability.stw_variance_coeff_gap hp0 hp1

/--
[stw_coeff_gap_eq_iff_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_coeff_gap_eq_iff_half_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  4 * p ^ 2 * (1 - p) ^ 2 = p * (1 - p) ↔ p = 1 / 2 := by
-- proof
  apply StatMech.Probability.stw_coeff_gap_eq_iff_half hp0 hp1

/--
[stw_pbiasedHCLib_implies_proved_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_pbiasedHCLib_implies_proved_lhs_eq
  {p ρ u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + (ρ ^ 2 + 1 - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 ≤ ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 := by
-- proof
  apply StatMech.Probability.stw_pbiasedHCLib_implies_proved_lhs hp0 hp1

/--
[stw_pbiasedHCLib_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_pbiasedHCLib_half_eq :
-- imply
  PBiasedHCLib (1 / 2) := by
-- proof
  apply StatMech.Probability.stw_pbiasedHCLib_half

/--
[stw_kkl_logGain_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_kkl_logGain_half_eq
  {ι : Type}
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.stw_kkl_logGain_half φ

/--
[stw_rhoOptimise_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_rhoOptimise_of_lib_eq
  {q : ℝ}
  {H : stw_RemainingGoal q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.stw_rhoOptimise_of_lib H

/--
[stw_sharpThreshold_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_sharpThreshold_of_lib_eq
  {q : ℝ}
  {H : stw_RemainingGoal q}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {v₀ L : ℝ}
-- given
  (hq1 : q ≤ 1)
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.Probability.stw_sharpThreshold_of_lib hq1 H A hA hq hv0 hL hhalf hvar hLL'

/--
[stw_RemainingGoal_empty_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_RemainingGoal_empty_window_eq
  {q : ℝ}
-- given
  (hq : q ≤ 1 / 2) :
-- imply
  stw_RemainingGoal q := by
-- proof
  apply StatMech.Probability.stw_RemainingGoal_empty_window hq

/--
[stw_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean)
-/
@[path]
private lemma stw_verdict_eq
  {u p : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1)
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hne : p ≠ 1 / 2) :
-- imply
  (1 < 2 - u ∧ 2 - u ≤ 2) ∧ (4 * p ^ 2 * (1 - p) ^ 2 < p * (1 - p)) := by
-- proof
  apply StatMech.Probability.stw_verdict hu0 hu1 hp0 hp1 hne


-- created on 2026-10-23
