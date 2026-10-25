/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part2
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


variable [IsFiniteMeasure μ]


def levelSet (T : α → α) (f : α → ℝ) (a b : ℝ) : Set α :=
  {x | fStarLow T f x < (a : EReal) ∧ (b : EReal) < fStar T f x}

end BirkhoffAE
end StatMech
