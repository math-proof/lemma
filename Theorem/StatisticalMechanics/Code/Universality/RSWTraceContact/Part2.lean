/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWTraceContact.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_ambientCrossingWalk_support_mem_pathVertices
    {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) {z : Site 2}
    (hz : z ∈ (rlc_ambientCrossingWalk gamma).support) :
    z ∈ rlc_pathVertices gamma := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  have hzMapped : z ∈ List.map hom gamma.2.2.1.support := by
    have hsupp := SimpleGraph.Walk.support_map hom gamma.2.2.1
    have hm := congrArg (fun l => z ∈ l) hsupp
    exact Eq.mp hm (by simpa [rlc_ambientCrossingWalk, hom] using hz)
  rw [List.mem_map] at hzMapped
  obtain ⟨u, hu, huz⟩ := hzMapped
  change (u : Site 2) = z at huz
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨u, hu, huz⟩


theorem rlc_mem_ambientCrossingWalk_support_iff_pathVertices
    {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) (z : Site 2) :
    z ∈ (rlc_ambientCrossingWalk gamma).support ↔
      z ∈ rlc_pathVertices gamma := by
  constructor
  · exact rlc_ambientCrossingWalk_support_mem_pathVertices gamma
  · intro hz
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
        hypercubicLattice 2 :=
      (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
        (rect a b c d)).toHom
    have huMapped : (u : Site 2) ∈ List.map hom gamma.2.2.1.support :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hsupp := SimpleGraph.Walk.support_map hom gamma.2.2.1
    exact Eq.mpr (congrArg (fun l => (u : Site 2) ∈ l) hsupp) huMapped


end Universality
end StatMech
