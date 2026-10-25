/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding


namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem finiteGraphEdge.dart_edge (edge : finiteGraphEdge G) :
    (edge.dart G).edge = edge.1 := by
  have hedgeSet : edge.1 ∈ G.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp edge.2
  have hcard := G.dart_edge_fiber_card edge.1 hedgeSet
  have hnonempty :
      ({dart : G.Dart | dart.edge = edge.1} : Finset G.Dart).Nonempty := by
    apply Finset.card_pos.mp
    omega
  exact Finset.mem_filter.mp hnonempty.choose_spec |>.2


end StatMech.FrontierA
