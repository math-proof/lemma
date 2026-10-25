/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.Ising.GibbsChoquet
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


variable {E : Type*}


theorem upTrue_isUpperSet (x : E) : IsUpperSet {ω : ConfigSpace E | ω x = true} := by
  intro a b hab ha
  simp only [Set.mem_setOf_eq] at *
  have h := hab x; rw [ha] at h
  cases hb : b x
  · rw [hb] at h; exact absurd h (by simp)
  · rfl


theorem upTrue_measurableSet (x : E) :
    MeasurableSet {ω : ConfigSpace E | ω x = true} := by
  have hpre : {ω : ConfigSpace E | ω x = true} = (ConfigSpace.eval x) ⁻¹' {true} := by
    ext ω; simp [ConfigSpace.eval]
  rw [hpre]; exact (ConfigSpace.measurable_eval x) (by trivial)


theorem upTrue_mem (x : E) : {ω : ConfigSpace E | ω x = true} ∈ upMeasSystem E :=
  ⟨upTrue_measurableSet x, upTrue_isUpperSet x⟩


theorem isPiSystem_upMeas : IsPiSystem (upMeasSystem E) := by
  rintro A ⟨hAm, hAu⟩ B ⟨hBm, hBu⟩ _
  exact ⟨hAm.inter hBm, hAu.inter hBu⟩


theorem generateFrom_upMeas :
    MeasurableSpace.generateFrom (upMeasSystem E)
      = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
  apply le_antisymm
  · apply generateFrom_le; rintro A ⟨hAm, _⟩; exact hAm
  · rw [ConfigSpace.measurableSpace_eq_iSup_comap]
    refine iSup_le (fun x => ?_)
    set G := MeasurableSpace.generateFrom (upMeasSystem E) with hG
    have hT : MeasurableSet[G] {ω : ConfigSpace E | ω x = true} :=
      measurableSet_generateFrom (upTrue_mem x)
    have hTc : MeasurableSet[G] {ω : ConfigSpace E | ω x = true}ᶜ := hT.compl
    have hEmpty : MeasurableSet[G] (∅ : Set (ConfigSpace E)) := @MeasurableSet.empty _ G
    intro s hs
    obtain ⟨t, _, rfl⟩ := hs
    classical
    have key : (ConfigSpace.eval x) ⁻¹' t
        = (if true ∈ t then {ω : ConfigSpace E | ω x = true} else ∅)
          ∪ (if false ∈ t then {ω : ConfigSpace E | ω x = true}ᶜ else ∅) := by
      ext ω
      simp only [Set.mem_preimage, ConfigSpace.eval_apply, Set.mem_union]
      cases hw : ω x <;> simp [hw]
    show MeasurableSet[G] _
    rw [key]
    refine (?_ : MeasurableSet[G] _).union (?_ : MeasurableSet[G] _)
    · split <;> [exact hT; exact hEmpty]
    · split <;> [exact hTc; exact hEmpty]


theorem StochasticallyDominated.antisymm {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : μ ≼ ν) (h₂ : ν ≼ μ) : μ = ν := by
  refine ext_of_generate_finite (upMeasSystem E)
    generateFrom_upMeas.symm isPiSystem_upMeas ?_ ?_
  · rintro A ⟨hAm, hAu⟩
    have hle : μ.real A ≤ ν.real A := h₁ A hAm hAu
    have hge : ν.real A ≤ μ.real A := h₂ A hAm hAu
    have hre : μ.real A = ν.real A := le_antisymm hle hge
    unfold Measure.real at hre
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp hre
  · rw [measure_univ, measure_univ]


theorem gibbs_unique_of_phases_eq {μm μp μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] [IsProbabilityMeasure μ]
    (hsw₁ : μm ≼ μ) (hsw₂ : μ ≼ μp) (hphase : μp = μm) :
    μ = μm := by
  have h₂ : μ ≼ μm := by rw [← hphase]; exact hsw₂
  exact StochasticallyDominated.antisymm h₂ hsw₁


theorem gibbs_sandwiched_eq_of_phases_eq {μm μp μ μ' : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hsw₁ : μm ≼ μ) (hsw₂ : μ ≼ μp) (hsw₁' : μm ≼ μ') (hsw₂' : μ' ≼ μp)
    (hphase : μp = μm) : μ = μ' := by
  rw [gibbs_unique_of_phases_eq hsw₁ hsw₂ hphase,
    gibbs_unique_of_phases_eq hsw₁' hsw₂' hphase]


end Ising
end StatMech
