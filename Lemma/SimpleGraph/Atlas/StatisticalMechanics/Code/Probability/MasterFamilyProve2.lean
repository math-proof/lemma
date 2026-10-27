import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve2.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[mfp2_singleBit_q_gt_2_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_singleBit_q_gt_2_false_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ mfp_SingleBitQGt2 (9 / 10) := by
-- proof
  apply StatMech.Probability.mfp2_singleBit_q_gt_2_false

/--
[mfp2_noiseGap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_noiseGap_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p u : ℝ}
-- given
  (hp : 1 / 2 < p)
  (_hp1 : p < 1)
  (_hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  0 < (1 - u) - (1 - u) * (4 * p * (1 - p)) := by
-- proof
  apply StatMech.Probability.mfp2_noiseGap_pos hp _hp1 _hu0 hu1

/--
[mfp2_summed_highNoise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_summed_highNoise_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (Hper : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))) :
-- imply
  (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
-- proof
  apply StatMech.Probability.mfp2_summed_highNoise hp0 hp1 φ Hper

/--
[mfp2_master_of_perCoordHighNoise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_master_of_perCoordHighNoise_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1)
  (Hper : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mfp2_master_of_perCoordHighNoise hp0 hp1 φ hu0 hu1 Hper

/--
[mfp2_openResidue_of_perCoordHighNoise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_openResidue_of_perCoordHighNoise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp2_PerCoordHighNoise q} :
-- imply
  frh_openResidue q := by
-- proof
  apply StatMech.Probability.mfp2_openResidue_of_perCoordHighNoise H

/--
[mfp2_perCoordHighNoise_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_perCoordHighNoise_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {e : ι}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (1 - u) ^ (S.erase e).card * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma (1 / 2 : ℝ)) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
-- proof
  apply StatMech.Probability.mfp2_perCoordHighNoise_half φ hu0 hu1 e

/--
[mfp2_master_half_via_perCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_master_half_via_perCoord_eq
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
  apply StatMech.Probability.mfp2_master_half_via_perCoord φ hu0 hu1

/--
[mfp2_perCoordHighNoise_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_perCoordHighNoise_nonvacuous_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
  {e : E}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ _S ∈ univ.filter (fun S : Finset E => e ∈ S), (0 : ℝ)) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
-- proof
  apply StatMech.Probability.mfp2_perCoordHighNoise_nonvacuous hp0 hp1 φ u e

/--
[mfp2_perCoordHighNoise_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_perCoordHighNoise_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp2_PerCoordHighNoise q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
  {e : E}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S), (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
-- proof
  apply StatMech.Probability.mfp2_perCoordHighNoise_noncirc H hp hp1 φ hu0 hu1 e

/--
[mfp2_kesten_of_perCoordHighNoise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_kesten_of_perCoordHighNoise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp2_PerCoordHighNoise q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.mfp2_kesten_of_perCoordHighNoise H hp hp1

/--
[mfp2_kkl_logGain_of_perCoordHighNoise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean)
-/
@[path]
private lemma mfp2_kkl_logGain_of_perCoordHighNoise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp2_PerCoordHighNoise q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mfp2_kkl_logGain_of_perCoordHighNoise H hp hp1 φ


-- created on 2026-10-23
