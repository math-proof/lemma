/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


def IsInvariantSet (T : α → α) (E : Set α) : Prop := ∀ x, x ∈ E ↔ T x ∈ E

end BirkhoffAE
end StatMech
