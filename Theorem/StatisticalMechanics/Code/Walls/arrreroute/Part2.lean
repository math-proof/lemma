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
import Def.StatisticalMechanics.Code.Walls.arrreroute
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem arr_offPatch_reachableK'_of_reroute {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) :
    ∀ f : Site 2, ¬ ats_faceHasCorner c f →
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  intro f hfc hf
  obtain ⟨p, hp⟩ := hR f hfc hf
  exact ats_reachable_insert_of_avoidWalk p hp


theorem arr_boundaryReachable_of_reroute_hook {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
  
  have hA' := arr_offPatch_reachableK'_of_reroute hR
  refine ats_boundaryReachable_insert_of_anchor (a₀ := a₀) ?_ ?_
  · 
    exact fun f hfc hf => hR f hfc hf
  · 
    intro f hfc hf
    exact arr_hookB_of_reachOffPatch hA' (hH f hfc hf)


theorem arr_attachStep_of_reroute_hook
    (h : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        fbc_BoundaryReachable (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        ∃ a₀ : Site 2, arr_ReRoute K c a₀ ∧ arr_Hook K c) :
    fbc_AttachStep := by
  intro K c hc hconn hhf hreach hconn' hhf' f g hf hg
  obtain ⟨a₀, hR, hH⟩ := h K c hc hconn hhf hreach hconn' hhf'
  exact arr_boundaryReachable_of_reroute_hook hR hH f g hf hg


end Walls
end StatMech
