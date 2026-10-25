/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc111routing.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc115_coarsePrecursor_of_coarseTrif (L : ℕ) {ω' : ConfigSpace (Sym2 (Site d))}
    (h : bc61_IsCoarseTrifurcation ω' L 0) :
    ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
      ω' ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  refine ⟨a₁, a₂, a₃, b₁, b₂, b₃, ⟨hb₁, hb₂, hb₃⟩, ⟨?_, ?_, ?_⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₁ a₁).mp hadj₁).1
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₂ a₂).mp hadj₂).1
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₃ a₃).mp hadj₃).1


theorem bc115_disconnected_of_distinctClusters (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hne : cluster d ω x ≠ cluster d ω y) :
    ¬ Connected d (removeSites T ω) x y := by
  intro hcut
  exact hne (cluster_eq_of_connected (connected_mono (daep_removeSites_le T ω) hcut))


theorem bc115_coarseTrif_disconnection_free (L : ℕ) {ω' : ConfigSpace (Sym2 (Site d))}
    (h : bc61_IsCoarseTrifurcation ω' L 0) :
    ∃ a₁ a₂ a₃ : Site d,
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₂ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₃ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, _, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hcut₁₂, hcut₁₃, hcut₂₃⟩


end StatMech.Walls
