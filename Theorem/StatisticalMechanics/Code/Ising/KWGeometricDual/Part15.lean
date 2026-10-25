/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part16
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_primalCut_card (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    (kwg_cutSet (kwg_primalEnds P) c).card = (cutEdges P.G c).card := by
  classical
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    rw [kwg_cutSet, Finset.mem_filter] at he
    rw [cutEdges, Finset.mem_filter]
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨e.2, (kwg_isSplit_iff_bond_neg c e.1).mp he.2⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro g hg
    have hgedge : g ∈ P.G.edgeSet := by
      rw [cutEdges, Finset.mem_filter] at hg
      rw [SimpleGraph.mem_edgeFinset] at hg
      exact hg.1
    let e : kwg_Edge P := ⟨g, hgedge⟩
    refine ⟨e, ?_, rfl⟩
    simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cutEdges, Finset.mem_filter] at hg
    exact (kwg_isSplit_iff_bond_neg c g).mpr hg.2


theorem kwg_primalEdgeFinset_cutSet (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) c) = cutEdges P.G c := by
  classical
  apply Finset.ext
  intro g
  constructor
  · intro hg
    rw [kwg_primalEdgeFinset, Finset.mem_map] at hg
    obtain ⟨e, he, rfl⟩ := hg
    rw [kwg_cutSet, Finset.mem_filter] at he
    rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨e.2, (kwg_isSplit_iff_bond_neg c e.1).mp he.2⟩
  · intro hg
    have hedge : g ∈ P.G.edgeSet := by
      rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hg
      exact hg.1
    let e : kwg_Edge P := ⟨g, hedge⟩
    rw [kwg_primalEdgeFinset, Finset.mem_map]
    refine ⟨e, ?_, rfl⟩
    simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cutEdges, Finset.mem_filter] at hg
    exact (kwg_isSplit_iff_bond_neg c g).mpr hg.2


theorem kwg_cutSet_eq_iff_cutEdges_eq (P : PlanarZ2Subgraph) (c d : ConfigSpace P.V) :
    kwg_cutSet (kwg_primalEnds P) c = kwg_cutSet (kwg_primalEnds P) d ↔
      cutEdges P.G c = cutEdges P.G d := by
  constructor
  · intro h
    rw [← kwg_primalEdgeFinset_cutSet P c, ← kwg_primalEdgeFinset_cutSet P d, h]
  · intro h
    apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
    simpa only [kwg_primalEdgeFinset] using
      (show kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) c) =
        kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) d) by
          rw [kwg_primalEdgeFinset_cutSet, kwg_primalEdgeFinset_cutSet, h])


end Ising
end StatMech
