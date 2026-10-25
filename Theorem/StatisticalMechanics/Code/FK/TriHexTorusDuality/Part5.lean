/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Instance.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem hexagonalTorusIndexedEdge_mem (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) :
    hexagonalTorusIndexedEdge L a ∈ (hexagonalTorusGraph L).edgeSet := by
  change (hexagonalTorusGraph L).Adj (a.1, false)
    (a.1 + hexagonalTorusStep L a.2, true)
  exact ⟨a, rfl⟩

end PeriodicPlanar
end FK
end StatMech
