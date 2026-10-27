import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
open Finset Real StatMech StatMech.Probability


/--
[fsm2_dampWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  0 ≤ fsm2_dampWeight p ρ φ e := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_nonneg p ρ φ e

/--
[fsm2_dampWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  fsm2_dampWeight p 1 φ e = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_one hp0 hp1 φ e

/--
[fsm2_dampWeight_le_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_le_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  fsm2_dampWeight p ρ φ e ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_le_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e

/--
[fsm2_dampWeight_le_infl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_le_infl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  fsm2_dampWeight p ρ φ e ≤ OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_le_infl hp0 hp1 h0 h1 φ e

/--
[fsm2_dampWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hρ : 0 < ρ)
  (hIe : 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) :
-- imply
  0 < fsm2_dampWeight p ρ φ e := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_pos hp0 hp1 hρ φ e hIe

/--
[fsm2_logSum_gain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_logSum_gain_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hρ : 0 < ρ)
  (_h1 : ρ ≤ 1)
  (_hq1 : 1 ≤ q)
  (_hq2 : q ≤ 2)
  (_hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
  (hpos : 0 < ∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) :
-- imply
  (∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) * Real.log ((∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) / (∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), fsm2_dampWeight p ρ φ e)) ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e * Real.log (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e / fsm2_dampWeight p ρ φ e) := by
-- proof
  apply StatMech.Probability.fsm2_logSum_gain hp0 hp1 hρ _h1 _hq1 _hq2 _hρsq φ hpos

/--
[fsm2_supp_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_supp_totalInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) = totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsm2_supp_totalInfl hp0 hp1 φ

/--
[fsm2_dampSupp_cap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampSupp_cap_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), fsm2_dampWeight p ρ φ e) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsm2_dampSupp_cap hp0 hp1 h0 h1 hq1 hq2 hρsq φ

/--
[fsm2_logGain_capped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_logGain_capped_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hρ : 0 < ρ)
  (h0 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
  (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (_hδ1 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < 1) :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (2 / q - 1) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e), OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e * Real.log (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e / fsm2_dampWeight p ρ φ e) := by
-- proof
  apply StatMech.Probability.fsm2_logGain_capped hp0 hp1 hρ h0 hq1 hq2 hρsq φ hTpos hδ0 _hδ1

/--
[fsm2_dampWeight_half_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_dampWeight_half_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  fsm2_dampWeight (1 / 2 : ℝ) 1 φ e = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.fsm2_dampWeight_half_one φ e

/--
[fsm2_rhoOptimise_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_rhoOptimise_of_residue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : fsm2_residue_statement q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.fsm2_rhoOptimise_of_residue H

/--
[fsm2_residue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean)
-/
@[path]
private lemma fsm2_residue_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsm2_residue_c0 hp0 hp1 φ


-- created on 2026-10-23
