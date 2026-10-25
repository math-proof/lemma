/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean -/

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
import Def.StatisticalMechanics.Code.Walls.fbcconnected.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem fbc_mem_tightSupport {K : Set (Site 2)} (hK : K.Finite) {f : Site 2} :
    f ∈ fbc_tightSupport hK ↔ f ∈ (faceBoundaryGraph K).support := by
  unfold fbc_tightSupport
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact boundarySupport_spec hK h

theorem fbc_tightSupport_covers {K : Set (Site 2)} (hK : K.Finite) :
    (faceBoundaryGraph K).support ⊆ (fbc_tightSupport hK : Set (Site 2)) := by
  intro f hf
  rw [Finset.mem_coe, fbc_mem_tightSupport]; exact hf


theorem fbc_faceBoundaryConnected_tight {K : Finset (Site 2)} (hne : K.Nonempty)
    (hfin : (↑K : Set (Site 2)).Finite)
    (hreach : fbc_BoundaryReachable (↑K : Set (Site 2))) :
    FaceBoundaryConnected (↑K : Set (Site 2)) (fbc_tightSupport hfin) := by
  obtain ⟨s, hs⟩ := fbc_support_nonempty hne
  apply fbc_connected_of_pairwise_reach ⟨s, (fbc_mem_tightSupport hfin).mpr hs⟩
  intro f hf g hg
  rw [fbc_mem_tightSupport] at hf hg
  obtain ⟨p⟩ := hreach f g hf hg
  refine ⟨p, ?_⟩
  
  clear hs s
  
  suffices hsuff : ∀ v ∈ p.support, v ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support by
    intro v hv; rw [fbc_mem_tightSupport]; exact hsuff v hv
  induction p with
  | nil =>
    intro v hv
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv; subst hv; exact hf
  | @cons a b c hab q ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hf
    · exact ih hab.symm.mem_support_left hg v hv


theorem fbc_single_dualCircuit_of_residue (h : fbc_BoundaryConnResidue)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K)
    (hhf : pc2_HoleFree (↑K : Set (Site 2))) (hfin : (↑K : Set (Site 2)).Finite)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (fbc_tightSupport hfin : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges := by
  have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
  have hreach := h K hconn hhf
  exact faceBoundaryGraph_single_dualCircuit (fbc_tightSupport_covers hfin)
    (fbc_faceBoundaryConnected_tight hne hfin hreach) hf₀


theorem fbc_boundaryReachable_box (m n : ℕ) :
    fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected (support_boxCluster_subset_frame m n)
    (pc2_box_faceBoundaryConnected m n)


theorem fbc_nonvacuous :
    fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ∧
      ∀ m n : ℕ, fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) :=
  ⟨fbc_boundaryReachable_singleton, fbc_boundaryReachable_box⟩


end Walls
end StatMech
