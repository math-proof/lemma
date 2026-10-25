/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.PathVisitsRow
open Set Finset SimpleGraph


namespace StatMech

namespace Lattice

theorem pvr_firstIdxAtCoord_spec {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) :
    (w.getVert (pvr_firstIdxAtCoord w k r h)) k = r :=
  Nat.find_spec h


theorem pvr_firstIdxAtCoord_min {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) {j : ℕ}
    (hj : j < pvr_firstIdxAtCoord w k r h) :
    (w.getVert j) k ≠ r :=
  Nat.find_min h hj


theorem pvr_firstAtRow {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 1 = c) (hbd : b 1 = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ i, (w.getVert i) 1 = r ∧ (∀ j, j < i → (w.getVert j) 1 ≠ r) := by
  have hex : ∃ i, (w.getVert i) 1 = r := by
    obtain ⟨i, _, hfi⟩ := pvr_exists_idx_at_coord w 1 hac hbd hcd r hr1 hr2
    exact ⟨i, hfi⟩
  refine ⟨pvr_firstIdxAtCoord w 1 r hex, pvr_firstIdxAtCoord_spec w 1 r hex, ?_⟩
  intro j hj
  exact pvr_firstIdxAtCoord_min w 1 r hex hj

end Lattice
end StatMech
