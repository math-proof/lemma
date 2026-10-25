/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedEntropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
import Def.StatisticalMechanics.Code.Probability.PBiasedEntropy.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem pen_rhoOptimise_of_damping {q : ℝ} (H : pen_DampingWitness q) : ptn_RhoOptimise q := by
  intro p hp hp1 E _ _ _ φ _Hcap
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg hprob f
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg hprob f
  
  set V := ∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2 with hVdef
  have hvarV : OSSS.var (OSSS.bernoulliWeight p) f = V := ptn_var_eq_fourierWeight hp0 hp1 f
  show 2 * OSSS.var (OSSS.bernoulliWeight p) f * Real.log (1 / δ) ≤ T
  rw [hvarV]
  rcases eq_or_lt_of_le (hvarV ▸ kkl_var_nonneg hprob f) with hV0 | hVpos
  · 
    rw [← hV0, mul_zero, zero_mul]; exact hTnn
  · 
    have hVarpos : 0 < OSSS.var (OSSS.bernoulliWeight p) f := by rw [hvarV]; exact hVpos
    obtain ⟨r, hr0, hr1, hDamp, hLog⟩ := H p hp hp1 φ hVarpos
    
    set D := ∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2 * r ^ S.card with hDdef
    have hDmass : pen_dampedMass p r f = D := rfl
    have hDpos : 0 < D := by rw [← hDmass]; exact pen_dampedMass_pos hr0 f hVpos
    
    have hext := pen_degree_extraction (univ.erase (∅ : Finset E))
      (fun S => (ptn_coeff p f S) ^ 2) (fun S => S.card) r hr0
      (fun S _ => sq_nonneg _) hDpos
    simp only [] at hext
    
    set M := ∑ S ∈ (univ.erase (∅ : Finset E)), (S.card : ℝ) * (ptn_coeff p f S) ^ 2 with hMdef
    have hMeq : M = (p * (1 - p)) * T := by
      rw [hMdef, hT]; exact pen_degreeWeight_eq hp0 hp1 φ
    
    have hextVDM : V * Real.log (V / D) ≤ Real.log (1 / r) * M := hext
    
    have hDampV : D ≤ δ * V := by rw [hδ, ← hvarV, ← hDmass]; exact hDamp
    
    exact pen_logGain_assembly (V := V) (D := D) (T := T) (δ := δ)
      (L := Real.log (1 / r)) (pp := p * (1 - p)) (M := M)
      hVpos hDpos hTnn hδnn (by nlinarith [hp0, hp1] : (0:ℝ) ≤ p * (1 - p)) hMeq
      hextVDM hDampV hLog


theorem pen_dampingWitness_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [zero_mul, zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _


theorem pen_dampingWitness_noncirc {q : ℝ} (H : pen_DampingWitness q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass p r (fun ω => if φ ω then (1 : ℝ) else 0)
        ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 :=
  H p hp hp1 φ hVar


theorem pen_kklHC_of_damping {q : ℝ} (H : pen_DampingWitness q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  ptn_kklHC_of_rhoOptimise (pen_rhoOptimise_of_damping H) hp hp1


theorem pen_PBiasedHC_of_damping {q : ℝ} (hq : q ≤ 1) (H : pen_DampingWitness q) :
    kpb_PBiasedHC q :=
  ptn_PBiasedHC_of_rhoOptimise hq (pen_rhoOptimise_of_damping H)

end StatMech.Probability
