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
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanFilling

open Kingman BirkhoffAE KingmanAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


def badSet (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) : Set α :=
  {x | ∀ m, 1 ≤ m → m ≤ N → (gLow T X x + ε) * m < X m x}


noncomputable def dep (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) (y : α) : ℝ :=
  gLow T X y + ε + (badSet T X ε N).indicator (fun z => X 1 z) y


noncomputable def badCost (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) (x : α) : ℝ :=
  (badSet T X ε N).indicator (fun z => X 1 z) x

end KingmanFilling
end StatMech
