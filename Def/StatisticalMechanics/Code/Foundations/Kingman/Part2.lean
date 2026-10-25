/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part2
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}


noncomputable def gamma (h : SubadditiveCocycle T μ X) : ℝ :=
  (subadditive_expSeq h).lim


end SubadditiveCocycle
end Kingman
end StatMech
