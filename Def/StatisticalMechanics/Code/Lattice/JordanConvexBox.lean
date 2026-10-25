/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ArcMonotonise
import Theorem.StatisticalMechanics.Code.Lattice.JordanConvexBox
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def jcb_monotoneArc_of_rowData {P : Set (Site 2)} {m m' c d : ℤ}
    (hcd : c ≤ d) (col : ℤ → ℤ)
    (hlo : ∀ r, c ≤ r → r ≤ d → m ≤ col r)
    (hhi : ∀ r, c ≤ r → r ≤ d → col r ≤ m')
    (hon : ∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ P)
    (hcorner : ∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ P)
    (hc1 : col (c - 1) = col c)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    JsiMonotoneArc P m m' c d where
  col := col
  band_lo := hlo
  band_hi := hhi
  shift := fun r _ _ => hshift r
  on_arc := by
    intro z hcz hzd hzcol _ _
    have hcell : jsi_cell (col (z 1)) (z 1) = z := by
      funext j; fin_cases j
      · show col (z 1) = z 0; rw [hzcol]
      · rfl
    rw [← hcell]; exact hon (z 1) hcz hzd
  cd := hcd
  shift_all := hshift
  corner := by
    intro z hcz hzd hzcol _ _
    have hcell : jsi_cell (col (z 1 - 1)) (z 1) = z := by
      funext j; fin_cases j
      · show col (z 1 - 1) = z 0; rw [hzcol]
      · rfl
    rw [← hcell]
    rcases eq_or_lt_of_le hcz with heq | hlt
    · rw [← heq, hc1]; exact hon c (le_refl c) hcd
    · exact hcorner (z 1) hlt hzd


end Lattice
end StatMech
