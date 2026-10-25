/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem atip2_plusState_invariant_zeroOne (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
    (plusState d β h : Measure (ConfigSpace (Site d))) s = 0
      ∨ (plusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
  have herg := aetc_plusState_isErgodic β h hd hβ hh hti hdlr
  rcases herg.2 s hs hinv with hz | hf
  · exact Or.inl hz
  · exact Or.inr (by rwa [measure_univ] at hf)


theorem atip2_minusState_invariant_zeroOne (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
    (minusState d β h : Measure (ConfigSpace (Site d))) s = 0
      ∨ (minusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
  have herg := aetc_minusState_isErgodic β h hd hβ hh hti hdlr
  rcases herg.2 s hs hinv with hz | hf
  · exact Or.inl hz
  · exact Or.inr (by rwa [measure_univ] at hf)


theorem atip2_plusState_ae_const (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    {β' : Type*} [Countable β'] [MeasurableSpace β'] [MeasurableSingletonClass β']
    (f : ConfigSpace (Site d) → β') (hf : Measurable f)
    (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
    ∃ k : β', (plusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 :=
  ConfigSpace.ergodic_ae_const_of_shiftInvariant
    (aetc_plusState_isErgodic β h hd hβ hh hti hdlr) f hf hinv


theorem atip2_minusState_ae_const (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    {β' : Type*} [Countable β'] [MeasurableSpace β'] [MeasurableSingletonClass β']
    (f : ConfigSpace (Site d) → β') (hf : Measurable f)
    (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
    ∃ k : β', (minusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 :=
  ConfigSpace.ergodic_ae_const_of_shiftInvariant
    (aetc_minusState_isErgodic β h hd hβ hh hti hdlr) f hf hinv


end Ising
end StatMech
