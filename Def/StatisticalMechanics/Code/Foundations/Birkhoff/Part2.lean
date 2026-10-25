/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Birkhoff
open MeasureTheory Filter Finset Function
open scoped Topology


namespace StatMech

namespace Birkhoff

variable {α : Type*} {T : α → α} {f : α → ℝ}


section MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}


variable [IsFiniteMeasure μ]


def maximalLevelSet (T : α → α) (f : α → ℝ) (a : ℝ) (n : ℕ) : Set α :=
  {x | 0 < maxBirkhoff T (fun y => f y - a) n x}


end MeasureTheory
end Birkhoff
end StatMech
