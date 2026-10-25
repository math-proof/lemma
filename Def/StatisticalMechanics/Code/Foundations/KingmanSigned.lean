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
open MeasureTheory Filter Topology ENNReal


namespace StatMech

namespace KingmanSigned

open Kingman BirkhoffAE KingmanAE KingmanFilling

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


noncomputable def addCoc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  birkhoffSum T (X 1) n x


noncomputable def Zc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else addCoc T X n x - X n x


noncomputable def Wc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else X n x - addCoc T X n x

end KingmanSigned
end StatMech
