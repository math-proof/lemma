import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.MaxInfluencePBiased.Part2
open Finset Real Set StatMech StatMech.BeffaraDC


/--
[maxInfl_ge_scaled_var_mul_log_card_of_logGain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfl_ge_scaled_var_mul_log_card_of_logGain_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p c : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hc0 : 0 ≤ c)
  (hc2 : c ≤ 2)
  (hgain : c * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ Probability.totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  (c / 2) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ Probability.maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.maxInfl_ge_scaled_var_mul_log_card_of_logGain hp0 hp1 hc0 hc2 φ hgain

/--
[pBiasedCorrection_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma pBiasedCorrection_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 ≤ pBiasedCorrection p := by
-- proof
  apply StatMech.BeffaraDC.pBiasedCorrection_nonneg hp0 hp1

/--
[pBiasedCorrection_le_one_sixteenth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma pBiasedCorrection_le_one_sixteenth_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  pBiasedCorrection p ≤ 1 / 16 := by
-- proof
  apply StatMech.BeffaraDC.pBiasedCorrection_le_one_sixteenth hp0 hp1

/--
[maxInfl_pbiased_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfl_pbiased_corrected_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ)) ≤ Probability.maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.maxInfl_pbiased_corrected hp0 hp1 φ

/--
[maxInfluence_pbiased_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_pbiased_corrected_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ e : E, StatMech.prob p A * (1 - StatMech.prob p A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ)) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_pbiased_corrected hp0 hp1 A

/--
[maxInfluence_qOne_compactWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_qOne_compactWindow_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ε p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hε0 : 0 < ε)
  (hp : p ∈ Set.Icc ε (1 - ε)) :
-- imply
  ∃ e : E, StatMech.prob p A * (1 - StatMech.prob p A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ)) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_qOne_compactWindow hε0 hp A

/--
[maxInfluence_pbiased_of_absorbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_pbiased_of_absorbed_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hcorr : 2 * (1 - 4 * p * (1 - p)) * (Probability.ptn_sigma p) ^ 2 * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))) ≤ 1) :
-- imply
  ∃ e : E, (1 / 2 : ℝ) * (StatMech.prob p A * (1 - StatMech.prob p A)) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_pbiased_of_absorbed hp0 hp1 A hcorr

/--
[maxInfluence_pbiased_largeInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_pbiased_largeInfl_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hlarge : Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ Probability.maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))) :
-- imply
  ∃ e : E, StatMech.prob p A * (1 - StatMech.prob p A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_pbiased_largeInfl hp0 hp1 A hlarge

/--
[maxInfluence_pbiased_of_hypercontractive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_pbiased_of_hypercontractive_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {H : Probability.KKLHypercontractive p 2}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ e : E, StatMech.prob p A * (1 - StatMech.prob p A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_pbiased_of_hypercontractive hp0 hp1 H A

/--
[maxInfluence_qOne_compactWindow_of_bkkkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean)
-/
@[path]
private lemma maxInfluence_qOne_compactWindow_of_bkkkl_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ε p : ℝ}
  {Hpb : Probability.kpb_PBiasedHC (1 - ε / 2)}
  {A : Set (ConfigSpace E)}
-- given
  (hε0 : 0 < ε)
  (hp : p ∈ Set.Icc ε (1 - ε)) :
-- imply
  ∃ e : E, StatMech.prob p A * (1 - StatMech.prob p A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_qOne_compactWindow_of_bkkkl hε0 hp Hpb A


-- created on 2026-10-23
