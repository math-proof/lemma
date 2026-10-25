/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean -/

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
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem pc2_box_faceBoundaryConnected (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) :=
  boxCluster_faceBoundaryConnected m n


theorem pc2_faceBoundaryConnected_of_anchor {K : Set (Site 2)} {T : Finset (Site 2)}
    {a₀ : Site 2} (ha₀ : a₀ ∈ T)
    (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T := by
  apply faceBoundaryConnected_of_walks ⟨a₀, ha₀⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := hwalk f hf
  obtain ⟨pg, hpg⟩ := hwalk g hg
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · exact hpg w (List.mem_of_mem_tail hwg)


theorem pc2_box_faceBoundaryConnected_via_anchor (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) :=
  pc2_faceBoundaryConnected_of_anchor (mem_boxFrame_corner m n)
    (fun _ hf => boxFrame_walk_from_corner m n hf)


end Lattice
end StatMech
