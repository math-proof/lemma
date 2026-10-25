/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem oddSubgraph_le (n : Current V) : oddSubgraph G n ≤ G :=
  fun _ _ h => h.1


theorem oddSubgraph_le_currentSubgraph (n : Current V) :
    oddSubgraph G n ≤ currentSubgraph G n := by
  intro x y ⟨hadj, hodd⟩
  exact ⟨hadj, hodd.pos⟩


end Sharpness
end StatMech
