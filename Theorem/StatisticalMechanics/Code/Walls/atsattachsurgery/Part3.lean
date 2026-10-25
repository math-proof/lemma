/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean -/

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
import Def.StatisticalMechanics.Code.Walls.atsattachsurgery.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ats_attachStep_of_patch (h : ats_AttachPatch) : fbc_AttachStep := by
  intro K c hc hconn hhf hreach hconn' hhf' f g hf hg
  exact h K c hc hconn hhf hreach hconn' hhf' f g hf hg


theorem ats_faceHasCorner_iff_mem_cornerFaces (c f : Site 2) :
    ats_faceHasCorner c f ↔ f ∈ cornerFaces c := by
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hceq : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
  unfold ats_faceHasCorner cornerFaces
  simp only [Finset.mem_insert, Finset.mem_singleton]
  conv_lhs => rw [hceq]
  
  conv_rhs => rw [hfeq]
  rw [site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega


theorem ats_boundaryReachable_insert_of_anchor {K : Finset (Site 2)} {c : Site 2}
    {a₀ : Site 2}
    (hA : ∀ f : Site 2, ¬ ats_faceHasCorner c f →
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
          ∀ w ∈ p.support, ¬ ats_faceHasCorner c w)
    (hB : ∀ f : Site 2, ats_faceHasCorner c f →
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
  
  have hreach_a0 : ∀ f : Site 2,
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
    intro f hf
    by_cases hcorner : ats_faceHasCorner c f
    · exact hB f hcorner hf
    · obtain ⟨p, hp⟩ := hA f hcorner hf
      exact ats_reachable_insert_of_avoidWalk p hp
  intro f g hf hg
  exact (hreach_a0 f hf).trans (hreach_a0 g hg).symm


end Walls
end StatMech
