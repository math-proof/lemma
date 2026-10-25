/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part2


namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteGraphEdge.edgeFlip_isSwap (edge : finiteGraphEdge G) :
    (edge.edgeFlip G).IsSwap := by
  rw [finiteGraphEdge.edgeFlip, Equiv.Perm.swap_isSwap_iff]
  exact (edge.dart G).symm_ne.symm

theorem finiteGraphEdge.dart_edge_ne {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') : (edge.dart G).edge ≠ (edge'.dart G).edge := by
  rw [finiteGraphEdge.dart_edge, finiteGraphEdge.dart_edge]
  exact fun h => hne (Subtype.ext h)

theorem finiteGraphEdge.edgeFlip_disjoint {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') :
    (edge.edgeFlip G).Disjoint (edge'.edgeFlip G) := by
  let a := edge.dart G
  let b := edge'.dart G
  have habEdge : a.edge ≠ b.edge :=
    finiteGraphEdge.dart_edge_ne G hne
  have hab : a ≠ b := fun h => habEdge (congrArg Dart.edge h)
  have habs : a ≠ b.symm := fun h =>
    habEdge (by rw [h, Dart.edge_symm])
  have hasb : a.symm ≠ b := fun h =>
    habEdge (by rw [← h, Dart.edge_symm])
  have hasbs : a.symm ≠ b.symm := fun h =>
    habEdge (by
      rw [← Dart.edge_symm a, ← Dart.edge_symm b, h])
  have hnodup : [a, a.symm, b, b.symm].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    exact ⟨⟨a.symm_ne.symm, hab, habs⟩,
      ⟨⟨hasb, hasbs⟩,
        ⟨b.symm_ne.symm, ⟨by simp, List.nodup_nil⟩⟩⟩⟩
  exact Equiv.Perm.disjoint_swap_swap hnodup

theorem finiteGraphEdge.edgeFlip_commute {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') :
    Commute (edge.edgeFlip G) (edge'.edgeFlip G) :=
  (finiteGraphEdge.edgeFlip_disjoint G hne).commute


end StatMech.FrontierA
