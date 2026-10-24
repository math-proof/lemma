import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.VarGapProve2
open Finset Real Set StatMech StatMech.Probability


/--
[vgp2_degWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_degWeight_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp2_degWeight_eq hp0 hp1 φ

/--
[vgp2_degWeight_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_degWeight_eq_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp2_degWeight_eq_half φ

/--
[vgp2_master_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_master_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.vgp2_master_half φ hu0 hu1

/--
[vgp2_filter_card_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_filter_card_ne_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (univ.filter (fun S : Finset ι => S.card ≠ 0)) = univ.erase (∅ : Finset ι) := by
-- proof
  apply StatMech.Probability.vgp2_filter_card_ne_zero

/--
[vgp2_kkl_logGain_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_kkl_logGain_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp2_kkl_logGain_half φ

/--
[vgp2_logGain_flex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_logGain_flex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  {d : κ → ℕ}
  {c : κ → ℝ}
  {δ : ℝ}
  {B : ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i)
  (hδ : 0 ≤ δ)
  (hB : 0 ≤ B)
  (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (∑ i : κ, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) ≤ δ ^ (u / (2 - u)) * B) :
-- imply
  2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ) ≤ B := by
-- proof
  apply StatMech.Probability.vgp2_logGain_flex hc hδ hB Hmaster

/--
[vgp2_kkl_logGain_of_master](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_kkl_logGain_of_master_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : frh_openResidue q}
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
  apply StatMech.Probability.vgp2_kkl_logGain_of_master H hp hp1 φ

/--
[vgp2_var_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_var_le_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
-- given
  (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδ1 : maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) / (2 * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
-- proof
  apply StatMech.Probability.vgp2_var_le_half φ hδ0 hδ1

/--
[vgp2_logGain_dictator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_logGain_dictator_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp2_logGain_dictator

/--
[vgp2_logGain_const_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve2.lean)
-/
@[path]
private lemma vgp2_logGain_const_nonvacuous_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι] :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp2_logGain_const_nonvacuous


-- created on 2026-10-23
