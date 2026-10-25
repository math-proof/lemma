/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Instance.StatisticalMechanics.Code.Lattice.JordanEulerSeparation
open SimpleGraph


set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*}


variable [Finite V] [DecidableEq V]


theorem jes_cycle_coe_connected {G : SimpleGraph V} {w : V} (c : G.Walk w w) :
    c.toSubgraph.coe.Connected :=
  Subgraph.connected_iff'.mp c.toSubgraph_connected


theorem jes_cycle_coe_nullity_one {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    nullity c.toSubgraph.coe = 1 :=
  jcs_cycle_nullity_eq_one c hc


theorem jes_cycle_delete_edge_isTree {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    ∃ (a b : ↑c.toSubgraph.verts),
      s(a, b) ∈ c.toSubgraph.coe.edgeSet ∧
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).Reachable a b ∧
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧
      c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b := by
  classical
  obtain ⟨a, b, he, hr⟩ :=
    jes_exists_closing_edge_of_nullity_one (jes_cycle_coe_nullity_one c hc)
  exact ⟨a, b, he, hr, jes_delete_closing_edge_isTree (jes_cycle_coe_connected c)
      (jes_cycle_coe_nullity_one c hc) he hr,
    deleteEdges_sup_edge_eq c.toSubgraph.coe a b he⟩


theorem jes_cycle_boundedRegionCount_one {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    jes_boundedRegionCount c.toSubgraph.coe = 1 :=
  jes_nullity_one_boundedRegionCount_one (jes_cycle_coe_nullity_one c hc)


theorem jes_cycle_faceCount_two {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 := by
  rw [jes_faceCount_eq_boundedRegionCount_add_one, jes_cycle_boundedRegionCount_one c hc]


theorem jes_cycle_is_tree_plus_closing_edge {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    ∃ (a b : ↑c.toSubgraph.verts),
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧
      c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b ∧
      jes_boundedRegionCount (c.toSubgraph.coe.deleteEdges {s(a, b)}) = 0 ∧
      jes_boundedRegionCount c.toSubgraph.coe = 1 := by
  obtain ⟨a, b, _, _, htree, heq⟩ := jes_cycle_delete_edge_isTree c hc
  exact ⟨a, b, htree, heq,
    jes_tree_boundedRegionCount_zero htree.isAcyclic,
    jes_cycle_boundedRegionCount_one c hc⟩


end Lattice
end StatMech
