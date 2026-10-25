/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourFinal
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem mem_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)} {f g : Site 2} :
    g ∈ componentSupport K T f ↔ g ∈ T ∧ (faceBoundaryGraph K).Reachable f g := by
  unfold componentSupport; rw [Finset.mem_filter]


theorem self_mem_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)} {f : Site 2}
    (hf : f ∈ T) : f ∈ componentSupport K T f := by
  rw [mem_componentSupport]; exact ⟨hf, SimpleGraph.Reachable.refl _⟩


theorem componentSupport_neighbor {K : Set (Site 2)} {T : Finset (Site 2)} {f g h : Site 2}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hg : g ∈ componentSupport K T f) (hadj : (faceBoundaryGraph K).Adj g h) :
    h ∈ componentSupport K T f := by
  rw [mem_componentSupport] at hg ⊢
  refine ⟨hsupp hadj.symm.mem_support_left, hg.2.trans hadj.reachable⟩


theorem componentSupport_walk_subset {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f g : Site 2}
    (hf : f ∈ T) (p : (faceBoundaryGraph K).Walk f g) :
    ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  intro v hv
  rw [mem_componentSupport]
  
  have hr : (faceBoundaryGraph K).Reachable f v := ⟨p.takeUntil v hv⟩
  refine ⟨?_, hr⟩
  
  by_cases hvf : v = f
  · rw [hvf]; exact hf
  · 
    have hr' : (faceBoundaryGraph K).Reachable v f := hr.symm
    obtain ⟨q2⟩ := hr'
    cases q2 with
    | nil => exact absurd rfl hvf
    | @cons _ c _ hadj2 _ => exact hsupp hadj2.mem_support_left


end Lattice
end StatMech
