/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.EntropySubadditivity.Part2
import Theorem.StatisticalMechanics.Code.Probability.GlobalLSI
import Def.StatisticalMechanics.Code.Probability.FSClose.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


variable {E : Type*} [Fintype E] [DecidableEq E]

theorem fsc2_dampingHard_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    esa_DampingHard q := by
  intro p hp hp1 E _ _ _ φ hVar hδpos hδsmall
  have hp0 : 0 < p := by have := hp.1; linarith
  
  obtain ⟨hr0pos, hr0lt1, hr0bal⟩ := esa_logBalance_threshold hp0 hp1
  
  have hfam : fsc2_EntMassFamily p φ := fsc2_entMassFamily_holds hp0 hp1 φ
  
  have hDamp := H p hp hp1 φ hVar hδpos hδsmall hfam
  
  refine ⟨Real.exp (-(1 / (2 * (p * (1 - p))))), hr0pos, hr0lt1, hDamp, ?_⟩
  exact le_of_eq hr0bal


theorem fsc2_dampingWitness_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    pen_DampingWitness q :=
  esa_dampingWitness_of_hard (fsc2_dampingHard_of_residue H)


theorem fsc2_rhoOptimise_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    ptn_RhoOptimise q :=
  esa_rhoOptimise_of_hard (fsc2_dampingHard_of_residue H)


theorem fsc2_PBiasedHC_of_residue {q : ℝ} (hq : q ≤ 1) (H : fsc2_DampingHardResidue q) :
    kpb_PBiasedHC q :=
  esa_PBiasedHC_of_hard hq (fsc2_dampingHard_of_residue H)


theorem fsc2_residue_nonvac {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool) :
    fsc2_EntMassFamily p φ :=
  fsc2_entMassFamily_holds hp0 hp1 φ


theorem fsc2_residue_noncirc {q : ℝ} (H : fsc2_DampingHardResidue q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδsmall : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      < Real.exp (-(1 / (2 * (p * (1 - p))))))
    (hfam : fsc2_EntMassFamily p φ) :
    pen_dampedMass p (Real.exp (-(1 / (2 * (p * (1 - p)))))) (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H p hp hp1 φ hVar hδpos hδsmall hfam

end StatMech.Probability
