/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE.Part4
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanFilling

open Kingman BirkhoffAE KingmanAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


noncomputable def gLow (T : α → α) (X : ℕ → α → ℝ) (x : α) : ℝ := (gStarLow T X x).toReal


end KingmanFilling
end StatMech
