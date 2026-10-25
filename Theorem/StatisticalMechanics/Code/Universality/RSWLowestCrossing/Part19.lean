/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Instance.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part5
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_iUnion_restrictedPathOpen (a b c d : ℤ) (L R : Set (Site 2)) :
    (⋃ gamma : RlcRestrictedCrossingPath a b c d L R,
      rlc_pathOpen gamma.1) = rlc_lrRestrictedEvent a b c d L R := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1.1, gamma.1.2.1, gamma.2.1, gamma.2.2,
      ⟨rlc_openWalkOfEdges omega gamma.1.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.1.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hx, hy, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma0 : RlcCrossingPath a b c d := ⟨x, y, q.toPath⟩
    let gamma : RlcRestrictedCrossingPath a b c d L R :=
      ⟨gamma0, hx, hy⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset hz
    have hedge : q.edges = q0.edges := rlc_edges_mapLe_eq hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2

end Universality
end StatMech
