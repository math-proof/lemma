/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_leftArmFrom_dependsOn (x : Site 2) (N : ℕ) :
    StatMech.DependsOn {omega | zfk_LeftArmFrom omega x N}
      (zih_leftSquareEdges N) := by
  intro omega omega' hagree
  have hcoord : ∀ a b : Site 2, a ∈ zfk_leftSquare N → b ∈ zfk_leftSquare N →
      omega s(a, b) = omega' s(a, b) := by
    intro a b ha hb
    symm
    apply hagree
    rw [Finset.mem_coe, zih_leftSquareEdges, mem_edgesWithinFinset]
    refine ⟨a, ?_, b, ?_, rfl⟩ <;>
      simpa [zih_leftSquareFinset, zfk_leftSquare] using ‹_›
  have hG : openSubgraphInduce 2 omega (zfk_leftSquare N) =
      openSubgraphInduce 2 omega' (zfk_leftSquare N) := by
    apply SimpleGraph.ext
    ext a b
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord a b a.2 b.2]
  unfold zfk_LeftArmFrom ConnectedWithin
  simp only [Set.mem_setOf_eq, hG]

end StatMech.TwoDim
