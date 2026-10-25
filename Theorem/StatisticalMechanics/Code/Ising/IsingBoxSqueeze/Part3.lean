/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.Ising.IsingBoxSqueeze.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem ibs_plusCylinderDecay_of_boundaryInfluence (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hd : 1 ≤ d) (hφ : StrictMono φ)
    (hbi : ibs_PlusBoundaryInfluence β h g φ) :
    pstc_PlusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨C, hC⟩ := hbi f hf
  exact ibs_decay_of_boundaryBound (fun n => plusMeasure d n β h) g f hd hφ C hC


theorem ibs_minusCylinderDecay_of_boundaryInfluence (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hd : 1 ≤ d) (hφ : StrictMono φ)
    (hbi : ibs_MinusBoundaryInfluence β h g φ) :
    pstc_MinusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨C, hC⟩ := hbi f hf
  exact ibs_decay_of_boundaryBound (fun n => minusMeasure d n β h) g f hd hφ C hC


theorem ibs_plusBoundaryInfluence_one (β h : ℝ) (φ : ℕ → ℕ) :
    ibs_PlusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  refine ⟨0, fun n => ?_⟩
  rw [pstc_decayFun_one]
  simp


theorem ibs_minusBoundaryInfluence_one (β h : ℝ) (φ : ℕ → ℕ) :
    ibs_MinusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  refine ⟨0, fun n => ?_⟩
  rw [pstc_decayFun_one]
  simp


theorem ibs_plusCylinderDecay_one_via_squeeze (β h : ℝ) {φ : ℕ → ℕ} (hd : 1 ≤ d)
    (hφ : StrictMono φ) :
    pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ :=
  ibs_plusCylinderDecay_of_boundaryInfluence β h (1 : Multiplicative (Site d)) φ hd hφ
    (ibs_plusBoundaryInfluence_one β h φ)


theorem ibs_plusState_isTranslationInvariant_of_boundaryInfluence (β h : ℝ) (hd : 1 ≤ d)
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        ibs_PlusBoundaryInfluence β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_isTranslationInvariant_of_cylinderDecay β h
    (fun g φ hφ hconv =>
      ibs_plusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))


theorem ibs_plusState_ergodic_extreme_of_boundaryInfluence (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        ibs_PlusBoundaryInfluence β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh
    (fun g φ hφ hconv =>
      ibs_plusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))


theorem ibs_minusState_ergodic_extreme_of_boundaryInfluence (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        ibs_MinusBoundaryInfluence β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_minusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh hdlr
    (fun g φ hφ hconv =>
      ibs_minusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))

end Ising
end StatMech
