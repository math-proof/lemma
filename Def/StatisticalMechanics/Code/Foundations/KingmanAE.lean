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
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


variable [IsFiniteMeasure μ]


noncomputable def remDom (X : ℕ → α → ℝ) (k : ℕ) (y : α) : ℝ :=
  ∑ r ∈ Finset.range k, (X r y)⁺

end KingmanAE
end StatMech
