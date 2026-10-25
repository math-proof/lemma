/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE.Part2
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


variable [IsFiniteMeasure μ]


@[nolint unusedArguments]
noncomputable def gStar (_T : α → α) (X : ℕ → α → ℝ) (x : α) : EReal :=
  limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop


@[nolint unusedArguments]
noncomputable def gStarLow (_T : α → α) (X : ℕ → α → ℝ) (x : α) : EReal :=
  liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop

end KingmanAE
end StatMech
