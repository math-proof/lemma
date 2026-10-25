/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part2
open Set Finset SimpleGraph
open StatMech.Ising


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_anchorRow_card (ℓ : ℕ) : (ccb_anchorRow ℓ).card ≤ ℓ := by
  unfold ccb_anchorRow
  exact le_trans Finset.card_image_le (by rw [Finset.card_range])


theorem mem_ccb_anchorRow {ℓ : ℕ} {v : Site 2} :
    v ∈ ccb_anchorRow ℓ ↔ ∃ j : ℕ, j < ℓ ∧ v = ![ (j : ℤ), 0] := by
  unfold ccb_anchorRow
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, Finset.mem_range.mpr hj, rfl⟩


end Lattice
end StatMech
