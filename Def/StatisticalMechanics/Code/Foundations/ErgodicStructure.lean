/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Theorem.StatisticalMechanics.Code.Foundations.ErgodicStructure
open MeasureTheory Filter Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace ErgodicStructure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


def InvariantsTrivial (T : α → α) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet[MeasurableSpace.invariants T] s → μ s = 0 ∨ μ s = 1


end ErgodicStructure
end StatMech
