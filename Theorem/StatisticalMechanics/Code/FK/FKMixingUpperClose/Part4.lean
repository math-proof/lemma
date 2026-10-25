/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Def.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part4
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_pairMixing_of_genMixing [DecidableEq E] (h : fmu_GenMixing (G := G) μ) :
    fmu_PairMixing (G := G) μ := by
  intro P δ hδ
  
  obtain ⟨g, hg⟩ := h (P.image fmu_multiOpen)
    (by intro A hA; rw [Finset.mem_image] at hA; obtain ⟨T, hT, rfl⟩ := hA
        exact fmu_multiOpen_mem_measurableCylinders T) δ hδ
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  exact hg (fmu_multiOpen T) (Finset.mem_image_of_mem _ hT)
    (fmu_multiOpen T') (Finset.mem_image_of_mem _ hT')


end FK
end StatMech
