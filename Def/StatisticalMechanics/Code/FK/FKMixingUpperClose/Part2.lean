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
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

noncomputable def fmu_traceInd (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) : ℝ :=
  if (∀ e ∈ F, ω e = τ e) then 1 else 0


noncomputable def fmu_traceCoef [DecidableEq E] (F : Finset E) (τ : E → Bool) (T : Finset E) : ℝ :=
  (∏ e ∈ T, (if τ e then (1:ℝ) else -1)) * (∏ e ∈ F \ T, (if τ e then (0:ℝ) else 1))


end FK
end StatMech
