/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Universality.STT.Part3
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

theorem sum_localWeight (p0 p1 p2 : ℝ) :
    ∑ ω : LocalConfig, localWeight p0 p1 p2 ω = 1 := by
  simp only [localWeight, edgeWeight, Fintype.sum_prod_type, Fintype.sum_bool, if_true,
    if_neg (by decide : ¬ (false = true))]
  ring


end Universality
end StatMech
