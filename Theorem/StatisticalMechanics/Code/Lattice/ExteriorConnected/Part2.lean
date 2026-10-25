/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.InteriorOrientation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Def.StatisticalMechanics.Code.Lattice.ExteriorConnected
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem exc_offSupport_of_reaches (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : exc_OffSupportReachesExterior K a) :
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
        (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) := by
  obtain ⟨R, hRbox, hreach⟩ := h
  intro z hzK hzsupp
  set F : Set (Site 2) := {z | z ∈ (mpl_orbitLoop K a).support} with hF
  obtain ⟨hz, e, he, hreach_ze⟩ := hreach z hzK hzsupp
  obtain ⟨p1, hp1⟩ := exc_reachable_compl_to_offSupport_walk F hz
    (exterior_subset_compl _ R hRbox he) hreach_ze
  obtain ⟨z0, p2, hp2, hfar⟩ := exc_exterior_reaches_farLeft F R hRbox e he
  refine ⟨z0, p1.append p2, ?_, ?_⟩
  · intro w hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with h | h
    · exact hp1 w h
    · exact hp2 w h
  · exact hfar


end Lattice
end StatMech
