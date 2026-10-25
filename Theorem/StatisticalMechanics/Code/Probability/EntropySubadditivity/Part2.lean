/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadditivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedEntropy.Part2
import Def.StatisticalMechanics.Code.Probability.EntropySubadditivity
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem esa_dampingWitness_of_hard {q : ℝ} (H : esa_DampingHard q) : pen_DampingWitness q := by
  intro p hp hp1 E _ _ _ φ hVar
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set σ2 := p * (1 - p) with hσ2
  have hσ2pos : 0 < σ2 := by rw [hσ2]; nlinarith
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set V := OSSS.var (OSSS.bernoulliWeight p) f with hV
  set r0 := Real.exp (-(1 / (2 * σ2))) with hr0def
  obtain ⟨hr0pos, hr0lt1, hr0bal⟩ := esa_logBalance_threshold hp0 hp1
  
  have hr0pos' : 0 < r0 := by rw [hr0def, hσ2]; exact hr0pos
  have hr0lt1' : r0 < 1 := by rw [hr0def, hσ2]; exact hr0lt1
  have hr0bal' : 4 * σ2 * Real.log (1 / r0) = 2 := by rw [hσ2, hr0def]; exact hr0bal
  
  have hδpos : 0 < δ :=
    esa_maxInfl_pos_of_var_pos (bernoulliWeight_isProbWeight hp0.le hp1.le) φ hVar
  
  have hVF : V = ∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2 := by
    rw [hV]; exact ptn_var_eq_fourierWeight hp0 hp1 f
  rcases le_or_gt r0 δ with hcase | hcase
  · 
    refine ⟨r0, hr0pos', hr0lt1', ?_, ?_⟩
    · have hle := esa_dampedMass_le (p := p) hr0pos' hr0lt1'.le f
      rw [← hVF] at hle
      calc pen_dampedMass p r0 f ≤ r0 * V := hle
        _ ≤ δ * V := mul_le_mul_of_nonneg_right hcase hVar.le
    · linarith [hr0bal']
  · 
    have hcase' : δ < Real.exp (-(1 / (2 * (p * (1 - p))))) := by rw [hσ2] at hr0def; rw [hr0def] at hcase; exact hcase
    exact H p hp hp1 φ hVar hδpos hcase'


theorem esa_rhoOptimise_of_hard {q : ℝ} (H : esa_DampingHard q) : ptn_RhoOptimise q :=
  pen_rhoOptimise_of_damping (esa_dampingWitness_of_hard H)


theorem esa_kklHC_of_hard {q : ℝ} (H : esa_DampingHard q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  pen_kklHC_of_damping (esa_dampingWitness_of_hard H) hp hp1


theorem esa_PBiasedHC_of_hard {q : ℝ} (hq : q ≤ 1) (H : esa_DampingHard q) :
    kpb_PBiasedHC q :=
  pen_PBiasedHC_of_damping hq (esa_dampingWitness_of_hard H)


theorem esa_dampingHard_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0)
        ≤ (1 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  obtain ⟨hr0pos, hr0lt1, hr0bal⟩ := esa_logBalance_threshold hp0 hp1
  refine ⟨Real.exp (-(1 / (2 * (p * (1 - p))))), hr0pos, hr0lt1, ?_, le_of_eq hr0bal⟩
  rw [one_mul, ptn_var_eq_fourierWeight hp0 hp1 f]
  have hle := esa_dampedMass_le (p := p) hr0pos hr0lt1.le f
  calc pen_dampedMass p _ f
      ≤ Real.exp (-(1 / (2 * (p * (1 - p))))) * (∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2) := hle
    _ ≤ (∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2) := by
        nlinarith [hr0lt1.le, Finset.sum_nonneg (fun (S : Finset E) (_ : S ∈ univ.erase (∅ : Finset E)) => sq_nonneg (ptn_coeff p f S)), hr0pos.le]


theorem esa_dampingHard_noncirc {q : ℝ} (H : esa_DampingHard q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδsmall : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      < Real.exp (-(1 / (2 * (p * (1 - p)))))) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0)
        ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 :=
  H p hp hp1 φ hVar hδpos hδsmall

end StatMech.Probability
