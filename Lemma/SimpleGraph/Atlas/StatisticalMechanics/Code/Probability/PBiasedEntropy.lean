import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedEntropy.Part2
open Finset Real StatMech StatMech.Probability


/--
[pen_dampedMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_dampedMass_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p r : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hr : 0 ≤ r) :
-- imply
  0 ≤ pen_dampedMass p r f := by
-- proof
  apply StatMech.Probability.pen_dampedMass_nonneg hr f

/--
[pen_dampedMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_dampedMass_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p r : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hr : 0 < r)
  (hV : 0 < ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2) :
-- imply
  0 < pen_dampedMass p r f := by
-- proof
  apply StatMech.Probability.pen_dampedMass_pos hr f hV

/--
[pen_degree_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_degree_extraction_eq
  [Fintype ι]
  [DecidableEq ι]
  {s : Finset κ}
  {c : κ → ℝ}
  {d : κ → ℕ}
  {r : ℝ}
-- given
  (hr0 : 0 < r)
  (hc : ∀ k ∈ s, 0 ≤ c k)
  (hD : 0 < ∑ k ∈ s, c k * r ^ (d k)) :
-- imply
  (∑ k ∈ s, c k) * Real.log ((∑ k ∈ s, c k) / (∑ k ∈ s, c k * r ^ (d k))) ≤ Real.log (1 / r) * ∑ k ∈ s, (d k : ℝ) * c k := by
-- proof
  apply StatMech.Probability.pen_degree_extraction s c d r hr0 hc hD

/--
[pen_logGain_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_logGain_assembly_eq
  [Fintype ι]
  [DecidableEq ι]
  {V D T δ L pp M : ℝ}
-- given
  (hV : 0 < V)
  (hD : 0 < D)
  (hT : 0 ≤ T)
  (hδ : 0 ≤ δ)
  (hpp : 0 ≤ pp)
  (hM : M = pp * T)
  (Hext : V * Real.log (V / D) ≤ L * M)
  (Hdamp : D ≤ δ * V)
  (Hlog : 4 * pp * L ≤ 2) :
-- imply
  2 * V * Real.log (1 / δ) ≤ T := by
-- proof
  apply StatMech.Probability.pen_logGain_assembly hV hD hT hδ hpp hM Hext Hdamp Hlog

/--
[pen_degreeWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_degreeWeight_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.pen_degreeWeight_eq hp0 hp1 φ

/--
[pen_rhoOptimise_of_damping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_rhoOptimise_of_damping_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : pen_DampingWitness q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.pen_rhoOptimise_of_damping H

/--
[pen_dampingWitness_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_dampingWitness_c0_eq
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
  apply StatMech.Probability.pen_dampingWitness_c0 hp0 hp1 φ

/--
[pen_dampingWitness_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_dampingWitness_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : pen_DampingWitness q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1)
  (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := by
-- proof
  apply StatMech.Probability.pen_dampingWitness_noncirc H hp hp1 φ hVar

/--
[pen_kklHC_of_damping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_kklHC_of_damping_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : pen_DampingWitness q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.pen_kklHC_of_damping H hp hp1

/--
[pen_PBiasedHC_of_damping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean)
-/
@[path]
private lemma pen_PBiasedHC_of_damping_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : pen_DampingWitness q}
-- given
  (hq : q ≤ 1) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.pen_PBiasedHC_of_damping hq H


-- created on 2026-10-23
