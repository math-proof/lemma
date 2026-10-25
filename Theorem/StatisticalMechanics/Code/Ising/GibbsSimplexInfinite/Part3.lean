/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.GibbsChoquet.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


variable {E : Type*}


theorem isPiSystem_clopenUp : IsPiSystem (clopenUpSystem E) := by
  rintro A ⟨hAc, hAu⟩ B ⟨hBc, hBu⟩ _
  exact ⟨hAc.inter hBc, hAu.inter hBu⟩


theorem upTrue_isClopen (x : E) : IsClopen {ω : ConfigSpace E | ω x = true} := by
  have hpre : {ω : ConfigSpace E | ω x = true} = (ConfigSpace.eval x) ⁻¹' {true} := by
    ext ω; simp [ConfigSpace.eval]
  rw [hpre]
  exact ⟨(isClosed_discrete _).preimage (continuous_apply x),
    (isOpen_discrete _).preimage (continuous_apply x)⟩


theorem upTrue_mem_clopen (x : E) : {ω : ConfigSpace E | ω x = true} ∈ clopenUpSystem E :=
  ⟨upTrue_isClopen x, upTrue_isUpperSet x⟩


theorem generateFrom_clopenUp [Countable E] :
    MeasurableSpace.generateFrom (clopenUpSystem E)
      = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
  apply le_antisymm
  · apply generateFrom_le; rintro A ⟨hAc, _⟩; exact hAc.2.measurableSet
  · rw [ConfigSpace.measurableSpace_eq_iSup_comap]
    refine iSup_le (fun x => ?_)
    set G := MeasurableSpace.generateFrom (clopenUpSystem E) with hG
    have hT : MeasurableSet[G] {ω : ConfigSpace E | ω x = true} :=
      measurableSet_generateFrom (upTrue_mem_clopen x)
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
    change MeasurableSet[G] _
    rw [key]
    refine (?_ : MeasurableSet[G] _).union (?_ : MeasurableSet[G] _)
    · split <;> [exact hT; exact hEmpty]
    · split <;> [exact hTc; exact hEmpty]


theorem gsi_clopen_antisymm [Countable E] {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : μ ≼c ν) (h₂ : ν ≼c μ) : μ = ν := by
  refine ext_of_generate_finite (clopenUpSystem E)
    generateFrom_clopenUp.symm isPiSystem_clopenUp ?_ ?_
  · rintro A ⟨hAc, hAu⟩
    have hre : μ.real A = ν.real A := le_antisymm (h₁ A hAc hAu) (h₂ A hAc hAu)
    unfold Measure.real at hre
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp hre
  · rw [measure_univ, measure_univ]


theorem gsi_gibbs_unique_of_phases_eq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ)
    (hphase : (plusState d β h : Measure (ConfigSpace (Site d)))
      = (minusState d β h : Measure (ConfigSpace (Site d)))) :
    μ = (minusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨hlow, hhigh⟩ := gsi_infinite_volume_sandwich β h hβ hh μ hμ
  have hhigh' : μ ≼c (minusState d β h : Measure (ConfigSpace (Site d))) := by
    rw [← hphase]; exact hhigh
  exact gsi_clopen_antisymm hhigh' hlow

end Ising
end StatMech
