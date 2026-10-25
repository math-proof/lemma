/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Foundations.Kingman
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}


noncomputable def expSeq (X : ℕ → α → ℝ) (μ : Measure α) (n : ℕ) : ℝ := ∫ x, X n x ∂μ


end SubadditiveCocycle
end Kingman
end StatMech
