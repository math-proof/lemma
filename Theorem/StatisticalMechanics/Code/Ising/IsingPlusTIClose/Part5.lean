/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem iti_cylinderAlg_le_decaySet (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) :
    Subalgebra.toSubmodule (pstc_cylinderAlg d) ≤ iti_decaySet β h g φ := by
  unfold pstc_cylinderAlg
  rw [Algebra.adjoin_eq_span, Submodule.span_le]
  intro hh hmem
  obtain ⟨T, rfl⟩ := iti_closure_isMonomial hmem
  change Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
      (BoundedContinuousFunction.mkOfCompact (iti_monomialCM T))) atTop (𝓝 0)
  exact iti_decayFun_monomial_tendsto_zero β h g φ hconv hhom T


theorem iti_plusCylinderDecay_of_homogeneous (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) :
    pstc_PlusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨hh, hhmem, rfl⟩ := hf
  exact iti_cylinderAlg_le_decaySet β h g φ hconv hhom hhmem


theorem iti_plusState_isTranslationInvariant_of_homogeneous (β h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_isTranslationInvariant_of_cylinderDecay β h
    (fun g φ _ hconv => iti_plusCylinderDecay_of_homogeneous β h g φ hconv (hhom g))


theorem iti_plusState_isErgodic_of_homogeneous_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isErgodic_of_upperDecay hβ h
    (iti_plusState_isTranslationInvariant_of_homogeneous β h hhom) hup


theorem iti_plusState_isInvariantExtremePoint_of_homogeneous_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isInvariantExtremePoint_of_upperDecay hβ h
    (iti_plusState_isTranslationInvariant_of_homogeneous β h hhom) hup

end Ising
end StatMech
