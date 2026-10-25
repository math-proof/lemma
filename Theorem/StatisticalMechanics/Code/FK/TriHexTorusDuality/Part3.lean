/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Instance.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triangularTorusIndexedEdge_mem (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) :
    triangularTorusIndexedEdge L a ∈ (triangularTorusGraph L).edgeSet := by
  change (triangularTorusGraph L).Adj a.1
    (a.1 + triangularTorusStep L a.2)
  exact ⟨a, rfl⟩

end PeriodicPlanar
end FK
end StatMech
