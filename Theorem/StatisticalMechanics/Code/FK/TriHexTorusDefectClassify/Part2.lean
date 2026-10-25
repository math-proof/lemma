/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Def.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

@[simp] theorem triHexTorusDualCutGraph_adj (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) (f g : HexTorusVertex L) :
    (triHexTorusDualCutGraph L K).Adj f g ↔
      (hexagonalTorusGraph L).Adj f g ∧
        triHexTorusPrimalOfDualEdge L s(f, g) ∉ K.edgeSet := Iff.rfl


theorem triHexTorus_openSub_dualConfig_graphEdgeConfig
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L)) :
    FK.openSub (hexagonalTorusGraph L)
        (triHexTorusDualConfig L (graphEdgeConfig K)) =
      triHexTorusDualCutGraph L K := by
  classical
  ext f g
  by_cases hfg : (hexagonalTorusGraph L).Adj f g
  · have he : s(f, g) ∈ (hexagonalTorusGraph L).edgeSet := by
      simpa only [SimpleGraph.mem_edgeSet]
    simp only [FK.openSub_adj, triHexTorusDualCutGraph_adj, hfg, true_and,
      triHexTorusDualConfig, dif_pos he, graphEdgeConfig]
    by_cases hmem : triHexTorusPrimalOfDualEdge L s(f, g) ∈ K.edgeSet <;>
      simp [hmem]
  · simp [FK.openSub_adj, triHexTorusDualCutGraph_adj, hfg]


theorem triHexTorusFaceCount_eq_dualCutGraph
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L)) :
    triHexTorusFaceCount L K =
      Nat.card (triHexTorusDualCutGraph L K).ConnectedComponent := by
  unfold triHexTorusFaceCount
  rw [triHexTorus_openSub_dualConfig_graphEdgeConfig]


end PeriodicPlanar
end FK
end StatMech
