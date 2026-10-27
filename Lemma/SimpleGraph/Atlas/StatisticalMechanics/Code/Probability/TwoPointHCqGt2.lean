import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.TwoPointHCqGt2.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[hcq_exponent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_exponent_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q' u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu1 : u < 1)
  (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) :
-- imply
  2 / q' - 1 ≤ u / (2 - u) := by
-- proof
  apply StatMech.Probability.hcq_exponent_le hp0 hp1 hu1 hrel

/--
[hcq_gap_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_gap_closedForm_eq
  [Fintype ι]
  [DecidableEq ι]
  {s u : ℝ}
-- given
  (hs0 : 0 < s)
  (hu1 : u < 1)
  (hslu : 0 < s + 1 - u) :
-- imply
  u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) = 2 * (1 - u) * (1 - s) / ((s + 1 - u) * (2 - u)) := by
-- proof
  apply StatMech.Probability.hcq_gap_closedForm hs0 hu1 hslu

/--
[hcq_gap_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_gap_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {s u : ℝ}
-- given
  (hs0 : 0 < s)
  (hs1 : s < 1)
  (hu_lo : 1 - s < u)
  (hu_hi : u < 1) :
-- imply
  u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ 2 * (1 - u) * (1 - s) / s := by
-- proof
  apply StatMech.Probability.hcq_gap_le hs0 hs1 hu_lo hu_hi

/--
[hcq_capped_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_capped_full_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hlo : 1 - 4 * p * (1 - p) ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) ∧ (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ 4 * (ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.hcq_capped_full hp0 hp1 φ hlo hu1

/--
[hcq_dom_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_dom_of_threshold_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ q' u : ℝ}
-- given
  (hδ0 : 0 < δ)
  (hthr : 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / q' - 1))) :
-- imply
  4 * (ptn_sigma p) ^ 2 * δ ^ (2 / q' - 1) ≤ δ ^ (u / (2 - u)) := by
-- proof
  apply StatMech.Probability.hcq_dom_of_threshold hδ0 hthr

/--
[hcq_star_of_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_star_of_dominates_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {q' : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hlo : 1 - 4 * p * (1 - p) ≤ u)
  (hu1 : u ≤ 1)
  (hq1 : 1 ≤ q')
  (hq2 : q' ≤ 2)
  (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
  (hdom : 4 * (ptn_sigma p) ^ 2 * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.hcq_star_of_dominates hp0 hp1 φ hlo hu1 hq1 hq2 hrel hdom

/--
[hcq_star_capped_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_star_capped_threshold_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {q' : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hlo : 1 - 4 * p * (1 - p) ≤ u)
  (hu1 : u < 1)
  (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hq1 : 1 ≤ q')
  (hq2 : q' ≤ 2)
  (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
  (hthr : 4 * (ptn_sigma p) ^ 2 ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u) - (2 / q' - 1))) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.hcq_star_capped_threshold hp0 hp1 φ hlo hu1 hδ0 hq1 hq2 hrel hthr

/--
[hcq_smallDelta_p_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_smallDelta_p_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.hcq_smallDelta_p_half φ hu0 hu1

/--
[hcq_smallDelta_of_lowRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_smallDelta_of_lowRange_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : hcq_lowRangeResidue q} :
-- imply
  cvg_smallDeltaResidue q := by
-- proof
  apply StatMech.Probability.hcq_smallDelta_of_lowRange H

/--
[hcq_martingaleHC_of_lowRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_martingaleHC_of_lowRange_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : hcq_lowRangeResidue q} :
-- imply
  mxd_martingaleHC_statement q := by
-- proof
  apply StatMech.Probability.hcq_martingaleHC_of_lowRange H

/--
[hcq_dominated_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_dominated_nonempty_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (_hδ0 : 0 < δ)
  (_hδ1 : δ ≤ 1) :
-- imply
  4 * (ptn_sigma p) ^ 2 ≤ δ ^ ((1 : ℝ) / (2 - 1) - (2 / (1 : ℝ) - 1)) := by
-- proof
  apply StatMech.Probability.hcq_dominated_nonempty hp0 hp1 _hδ0 _hδ1

/--
[hcq_threshold_of_gap_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_threshold_of_gap_small_eq
  [Fintype ι]
  [DecidableEq ι]
  {s δ g : ℝ}
-- given
  (hs0 : 0 < s)
  (hδ0 : 0 < δ)
  (hδ1 : δ < 1)
  (hgle : g ≤ Real.log (1 / s) / Real.log (1 / δ)) :
-- imply
  s ≤ δ ^ g := by
-- proof
  apply StatMech.Probability.hcq_threshold_of_gap_small hs0 hδ0 hδ1 hgle

/--
[hcq_residue_proper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_residue_proper_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ : ℝ}
-- given
  (hp : 1 / 2 < p)
  (hp1 : p < 1)
  (hδ0 : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  ∃ u : ℝ, (0 < u ∧ u < 1) ∧ 1 - 4 * p * (1 - p) ≤ u ∧ 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1)) := by
-- proof
  apply StatMech.Probability.hcq_residue_proper hp hp1 hδ0 hδ1

/--
[hcq_antecedent_not_tautology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_antecedent_not_tautology_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ : ℝ}
-- given
  (hp : 1 / 2 < p)
  (hp1 : p < 1)
  (hδ0 : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  ∃ u : ℝ, (0 < u ∧ u < 1) ∧ ¬ (u < 1 - 4 * p * (1 - p) ∨ δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1)) < 4 * (ptn_sigma p) ^ 2) := by
-- proof
  apply StatMech.Probability.hcq_antecedent_not_tautology hp hp1 hδ0 hδ1

/--
[hcq_lowRange_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean)
-/
@[path]
private lemma hcq_lowRange_nonvacuous_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (_hu0 : 0 < u)
  (_hu1 : u < 1) :
-- imply
  (0 : ℝ) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.hcq_lowRange_nonvacuous hp0 hp1 φ _hu0 _hu1


-- created on 2026-10-23
