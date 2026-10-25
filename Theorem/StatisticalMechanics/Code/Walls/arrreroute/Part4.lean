/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Def.StatisticalMechanics.Code.Walls.arrreroute.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem arr_avoidWalk_of_induceReachable {K : Finset (Site 2)} {c f a₀ : Site 2}
    (hf : f ∈ arr_offPatchSet c) (ha₀ : a₀ ∈ arr_offPatchSet c)
    (h : ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
        ⟨f, hf⟩ ⟨a₀, ha₀⟩) :
    ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ p.support, ¬ ats_faceHasCorner c w := by
  obtain ⟨q⟩ := h
  refine ⟨q.map (SimpleGraph.Embedding.induce
    (G := faceBoundaryGraph (↑K : Set (Site 2))) (arr_offPatchSet c)).toHom, ?_⟩
  intro w hw
  have hw2 : w ∈ List.map (⇑(SimpleGraph.Embedding.induce
      (G := faceBoundaryGraph (↑K : Set (Site 2))) (arr_offPatchSet c)).toHom) q.support := by
    rwa [← SimpleGraph.Walk.support_map]
  obtain ⟨v, _, hvw⟩ := List.mem_map.mp hw2
  rw [← hvw]; exact v.2


theorem arr_reRoute_of_induceReachable {K : Finset (Site 2)} {c a₀ : Site 2}
    (ha₀ : a₀ ∈ arr_offPatchSet c)
    (h : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c),
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
          ⟨f, hfc⟩ ⟨a₀, ha₀⟩) :
    arr_ReRoute K c a₀ := by
  intro f hfc hf
  exact arr_avoidWalk_of_induceReachable hfc ha₀ (h f hfc hf)


theorem arr_faithful_tromino :
    insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧
      fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  ⟨ats_insert_domino_eq_tromino, ats_tromino_boundaryReachable⟩


end Walls
end StatMech
