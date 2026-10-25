/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


noncomputable def fStar (T : α → α) (f : α → ℝ) (x : α) : EReal :=
  limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop


noncomputable def fStarLow (T : α → α) (f : α → ℝ) (x : α) : EReal :=
  liminf (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop

end BirkhoffAE
end StatMech
