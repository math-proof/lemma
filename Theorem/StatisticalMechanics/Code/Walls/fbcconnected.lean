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
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem fbc_connected_of_common_reach {K : Set (Site 2)} {T : Finset (Site 2)}
    {a₀ : Site 2} (ha₀ : a₀ ∈ T)
    (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T :=
  pc2_faceBoundaryConnected_of_anchor ha₀ hwalk


theorem fbc_connected_of_pairwise_reach {K : Set (Site 2)} {T : Finset (Site 2)}
    (hne : T.Nonempty)
    (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g,
        ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T :=
  faceBoundaryConnected_of_walks hne hwalk


theorem fbc_walk_support_in_boundarySupport {K : Set (Site 2)} (hK : K.Finite)
    {f g : Site 2} (p : (faceBoundaryGraph K).Walk f g)
    (hf : f ∈ (boundarySupport hK : Set (Site 2))) (hg : g ∈ (boundarySupport hK : Set (Site 2)))
    (v : Site 2) (hv : v ∈ p.support) : v ∈ boundarySupport hK := by
  
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv; exact hf
  | @cons a b c hab q ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · 
      exact hf
    · 
      have hbmem : b ∈ (boundarySupport hK : Set (Site 2)) :=
        boundarySupport_spec hK hab.symm.mem_support_left
      exact ih hbmem hg hv


theorem fbc_connected_of_reachable {K : Set (Site 2)} (hK : K.Finite)
    (hne : (boundarySupport hK).Nonempty)
    (hreach : ∀ f ∈ (boundarySupport hK : Set (Site 2)), ∀ g ∈ (boundarySupport hK : Set (Site 2)),
      (faceBoundaryGraph K).Reachable f g) :
    FaceBoundaryConnected K (boundarySupport hK) := by
  apply fbc_connected_of_pairwise_reach hne
  intro f hf g hg
  obtain ⟨p⟩ := hreach f (by exact_mod_cast hf) g (by exact_mod_cast hg)
  refine ⟨p, ?_⟩
  intro v hv
  have := fbc_walk_support_in_boundarySupport hK p (by exact_mod_cast hf) (by exact_mod_cast hg) v hv
  exact_mod_cast this


end Walls
end StatMech
