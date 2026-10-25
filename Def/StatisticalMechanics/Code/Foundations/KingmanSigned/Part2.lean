/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean -/

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
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.KingmanSigned
open MeasureTheory Filter Topology ENNReal


namespace StatMech

namespace KingmanSigned

open Kingman BirkhoffAE KingmanAE KingmanFilling

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


noncomputable def Sc (T : α → α) (X : ℕ → α → ℝ) (M : ℝ) (n : ℕ) (x : α) : ℝ :=
  X n x + (M * n - addCoc T X n x)


noncomputable def Vc (T : α → α) (X : ℕ → α → ℝ) (M : ℝ) (n : ℕ) (x : α) : ℝ :=
  (Sc T X M n x)⁺

end KingmanSigned
end StatMech
