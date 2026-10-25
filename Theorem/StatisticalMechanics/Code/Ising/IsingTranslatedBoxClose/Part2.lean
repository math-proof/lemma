/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap.Part2
import Def.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem itb_boundaryDecay_of_homogeneous (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hhom : iti_PlusMultiHomogeneous β h g) :
    itb_PlusMultiBoundaryDecay β h g φ := by
  intro T
  have h1 := iti_plus_multiOpen_tendsto β h φ T hconv
  have h2 := iti_plus_multiOpen_tendsto β h φ (T.image (fun x => g⁻¹ • x)) hconv
  have hsub := h1.sub h2
  rw [← hhom T, sub_self] at hsub
  exact hsub


theorem itb_homogeneous_of_boundaryDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hdecay : itb_PlusMultiBoundaryDecay β h g φ) :
    iti_PlusMultiHomogeneous β h g := by
  intro T
  have h1 := iti_plus_multiOpen_tendsto β h φ T hconv
  have h2 := iti_plus_multiOpen_tendsto β h φ (T.image (fun x => g⁻¹ • x)) hconv
  have hdiff := h1.sub h2
  have heq := tendsto_nhds_unique hdiff (hdecay T)
  linarith [heq]


theorem itb_plusMultiBoundaryDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    itb_PlusMultiBoundaryDecay β h (1 : Multiplicative (Site d)) φ := by
  intro T
  have hTeq : T.image (fun x => (1 : Multiplicative (Site d))⁻¹ • x) = T := by
    rw [Finset.image_congr (g := id) (fun x _ => by simp), Finset.image_id]
  simp only [hTeq, sub_self]
  exact tendsto_const_nhds


end Ising
end StatMech
