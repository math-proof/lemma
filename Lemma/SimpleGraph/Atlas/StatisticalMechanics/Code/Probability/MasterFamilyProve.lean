import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.MasterFamilyProve
open Finset Real Set StatMech StatMech.Probability


/--
[mfp_chord_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_chord_bound_eq
  [Fintype ι]
  [DecidableEq ι]
  {G : ℝ → ℝ}
  {u anc : ℝ}
-- given
  (hG : ConvexOn ℝ (Icc (0:ℝ) 1) G)
  (ha0 : 0 < anc)
  (ha1 : anc ≤ 1)
  (hu0 : 0 ≤ u)
  (hua : u ≤ anc) :
-- imply
  G u ≤ (1 - u / anc) * G 0 + (u / anc) * G anc := by
-- proof
  apply StatMech.Probability.mfp_chord_bound hG ha0 ha1 hu0 hua

/--
[mfp_L_chord_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_L_chord_bound_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ ((1 - u) + u * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mfp_L_chord_bound hp0 hp1 φ hu0 hu1

/--
[mfp_chord_route_dead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_chord_route_dead_eq
  [Fintype ι]
  [DecidableEq ι]
  {T : ℝ}
-- given
  (hT : 0 < T) :
-- imply
  Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T < (1 - (1:ℝ) / 2) * T := by
-- proof
  apply StatMech.Probability.mfp_chord_route_dead hT

/--
[mfp_chord_gap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_chord_gap_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {T : ℝ}
-- given
  (hT : 0 < T) :
-- imply
  0 < (1 - (1:ℝ) / 2) * T - Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T := by
-- proof
  apply StatMech.Probability.mfp_chord_gap_pos hT

/--
[mfp_singleBit_q_gt_2_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_singleBit_q_gt_2_value_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  mfp_SingleBitQGt2 (1 / 2) := by
-- proof
  apply StatMech.Probability.mfp_singleBit_q_gt_2_value

/--
[mfp_singleBit_route_dead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_singleBit_route_dead_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {H : mfp_SingleBitQGt2 p}
  {u : ℝ}
  {u₀ v₀ : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  ((1 - p) * u₀ + p * v₀) ^ 2 + (1 - u) * (p * (1 - p)) * (u₀ - v₀) ^ 2 ≤ ((1 - p) * |u₀| ^ (2 - u) + p * |v₀| ^ (2 - u)) ^ (2 / (2 - u)) := by
-- proof
  apply StatMech.Probability.mfp_singleBit_route_dead H hu0 hu1 u₀ v₀

/--
[mfp_kkl_logGain_of_masterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_kkl_logGain_of_masterFamily_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp_masterFamily q}
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
  apply StatMech.Probability.mfp_kkl_logGain_of_masterFamily H hp hp1 φ

/--
[mfp_martingaleHC_of_masterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_martingaleHC_of_masterFamily_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp_masterFamily q} :
-- imply
  mxd_martingaleHC_statement q := by
-- proof
  apply StatMech.Probability.mfp_martingaleHC_of_masterFamily H

/--
[mfp_kesten_of_masterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_kesten_of_masterFamily_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp_masterFamily q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.mfp_kesten_of_masterFamily H hp hp1

/--
[mfp_masterFamily_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_masterFamily_half_eq
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
  apply StatMech.Probability.mfp_masterFamily_half φ hu0 hu1

/--
[mfp_masterFamily_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_masterFamily_nonvacuous_eq
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
  (hp1 : p ≤ 1) :
-- imply
  (0 : ℝ) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mfp_masterFamily_nonvacuous hp0 hp1 φ u

/--
[mfp_masterFamily_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean)
-/
@[path]
private lemma mfp_masterFamily_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mfp_masterFamily q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mfp_masterFamily_noncirc H hp hp1 φ hu0 hu1


-- created on 2026-10-23
