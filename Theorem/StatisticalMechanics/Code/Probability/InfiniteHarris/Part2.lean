/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Probability.InfiniteHarris
open MeasureTheory Set Filter
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

theorem ih_fill_mono (F : Finset E) : Monotone (ih_fill F) := by
  intro eta eta' h e
  simp only [ih_fill]
  split
  · exact h _
  · exact le_rfl

end StatMech
