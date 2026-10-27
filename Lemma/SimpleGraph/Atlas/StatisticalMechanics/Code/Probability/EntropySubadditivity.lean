import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.EntropySubadditivity.Part2
open Finset Real StatMech StatMech.Probability


/--
[esa_dampedMass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_dampedMass_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {p r : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r ≤ 1) :
-- imply
  pen_dampedMass p r f ≤ r * (∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2) := by
-- proof
  apply StatMech.Probability.esa_dampedMass_le hr0 hr1 f

/--
[esa_logBalance_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_logBalance_threshold_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < Real.exp (-(1 / (2 * (p * (1 - p))))) ∧ Real.exp (-(1 / (2 * (p * (1 - p))))) < 1 ∧ 4 * (p * (1 - p)) * Real.log (1 / Real.exp (-(1 / (2 * (p * (1 - p)))))) = 2 := by
-- proof
  apply StatMech.Probability.esa_logBalance_threshold hp0 hp1

/--
[esa_maxInfl_pos_of_var_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_maxInfl_pos_of_var_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hν : OSSS.IsProbWeight ν)
  (hVar : 0 < OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  0 < maxInfl ν (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.esa_maxInfl_pos_of_var_pos hν φ hVar

/--
[esa_dampingWitness_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_dampingWitness_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q} :
-- imply
  pen_DampingWitness q := by
-- proof
  apply StatMech.Probability.esa_dampingWitness_of_hard H

/--
[esa_rhoOptimise_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_rhoOptimise_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.esa_rhoOptimise_of_hard H

/--
[esa_kklHC_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_kklHC_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.esa_kklHC_of_hard H hp hp1

/--
[esa_PBiasedHC_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_PBiasedHC_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
-- given
  (hq : q ≤ 1) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.esa_PBiasedHC_of_hard hq H

/--
[esa_dampingHard_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_dampingHard_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0) ≤ (1 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := by
-- proof
  apply StatMech.Probability.esa_dampingHard_c0 hp0 hp1 φ

/--
[esa_dampingHard_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean)
-/
@[path]
private lemma esa_dampingHard_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1)
  (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδsmall : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-(1 / (2 * (p * (1 - p)))))) :
-- imply
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := by
-- proof
  apply StatMech.Probability.esa_dampingHard_noncirc H hp hp1 φ hVar hδpos hδsmall


-- created on 2026-10-23
