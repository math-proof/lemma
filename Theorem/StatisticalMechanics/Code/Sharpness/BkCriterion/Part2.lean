/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Sharpness.BkCriterion
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace


variable {E : Type*}


variable {V : Type*}


lemma openSub_mono (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω') :
    openSub G ω ≤ openSub G ω' := by
  intro x y ⟨hadj, hopen⟩
  refine ⟨hadj, ?_⟩
  have hb := h s(x, y)
  rw [hopen] at hb
  exact le_antisymm le_top hb


end Sharpness
end StatMech
