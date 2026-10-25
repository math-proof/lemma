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
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


def fmu_multiOpen (T : Finset E) : Set (ConfigSpace E) := {ω | ∀ e ∈ T, ω e = true}


noncomputable def fmu_xR (ω : ConfigSpace E) (e : E) : ℝ := if ω e then 1 else 0


noncomputable def fmu_moInd (T : Finset E) (ω : ConfigSpace E) : ℝ := ∏ e ∈ T, fmu_xR ω e


end FK
end StatMech
