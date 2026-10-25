/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


def pweight [Fintype E] (φ : E → Bool → ℝ) (ω : ConfigSpace E) : ℝ := ∏ x, φ x (ω x)


end StatMech
