/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


theorem bddAbove_range_apply (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : BddAbove (Set.range (fun n => (μ n) A)) :=
  ⟨1, by rintro x ⟨n, rfl⟩; exact apply_le_one _ _⟩


end FK
end StatMech
