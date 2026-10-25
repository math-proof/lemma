/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem reachable_induce_of_walk_in_support {K : Set (Site 2)} {T : Finset (Site 2)}
    {f g : Site 2} (p : (faceBoundaryGraph K).Walk f g)
    (hsub : ∀ v ∈ p.support, v ∈ T) (hf : f ∈ T) :
    ((faceBoundaryGraph K).induce (T : Set (Site 2))).Reachable ⟨f, hf⟩
      ⟨g, hsub g p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab q ih =>
    
    have hbT : b ∈ T := hsub b (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsub : ∀ v ∈ q.support, v ∈ T := by
      intro v hv
      exact hsub v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
    
    have hadjI : ((faceBoundaryGraph K).induce (T : Set (Site 2))).Adj ⟨a, hf⟩ ⟨b, hbT⟩ := by
      rw [SimpleGraph.induce_adj]; exact hab
    have hrec := ih hqsub hbT
    exact (SimpleGraph.Adj.reachable hadjI).trans hrec


theorem faceBoundaryConnected_of_walks {K : Set (Site 2)} {T : Finset (Site 2)}
    (hne : T.Nonempty)
    (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g,
        ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T := by
  rw [FaceBoundaryConnected]
  have hnonempty : Nonempty (T : Set (Site 2)) := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨⟨t, ht⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, hnonempty⟩
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  obtain ⟨p, hp⟩ := hwalk f hf g hg
  have := reachable_induce_of_walk_in_support p hp hf
  
  convert this using 2


theorem mem_singletonOrigin (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ↔ p = 0 ∧ q = 0 := by
  rw [Finset.mem_coe, Finset.mem_singleton, origin_eq_zerozero, site2_eq]


end Lattice
end StatMech
