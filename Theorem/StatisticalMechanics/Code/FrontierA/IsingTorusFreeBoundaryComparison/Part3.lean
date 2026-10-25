/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem mk_mem_finiteCutInternalEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutInternalEdges G S ↔
      G.Adj x y ∧ x ∈ S ∧ y ∈ S := by
  simp [finiteCutInternalEdges, ghsvp_vertexEdges, Sharpness.edgeInside,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

@[simp] theorem mk_mem_finiteCutExteriorEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutExteriorEdges G S ↔
      G.Adj x y ∧ x ∉ S ∧ y ∉ S := by
  simp [finiteCutExteriorEdges, ghsvp_vertexEdges, Sharpness.edgeInside,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

@[simp] theorem mk_mem_finiteCutCrossEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutCrossEdges G S ↔
      G.Adj x y ∧ ((x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S)) := by
  simp only [finiteCutCrossEdges, Finset.mem_sdiff, Finset.mem_union,
    mk_mem_finiteCutInternalEdges_iff, mk_mem_finiteCutExteriorEdges_iff,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hxy, hnot⟩
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (hnot (Or.inl ⟨hxy, hx, hy⟩)).elim
    · exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨hxy, Or.inr ⟨hx, hy⟩⟩
    · exact (hnot (Or.inr ⟨hxy, hx, hy⟩)).elim
  · rintro ⟨hxy, hcross⟩
    refine ⟨hxy, ?_⟩
    rcases hcross with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rintro (⟨_, _, hy'⟩ | ⟨_, hx', _⟩)
      · exact hy hy'
      · exact hx' hx
    · rintro (⟨_, hx', _⟩ | ⟨_, _, hy'⟩)
      · exact hx hx'
      · exact hy' hy


end
end StatMech.FrontierA
