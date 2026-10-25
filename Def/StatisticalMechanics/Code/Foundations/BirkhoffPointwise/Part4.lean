/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part3
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


variable [IsFiniteMeasure μ]


noncomputable def birkhoffLimit (T : α → α) (f : α → ℝ) (x : α) : ℝ := (fStar T f x).toReal


end BirkhoffAE
end StatMech
