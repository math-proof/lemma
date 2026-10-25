/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexBoundaryAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


@[simp]
theorem hexRegionCls_start (R : HexRegion) : hexRegionCls R R.start = 0 := by
  unfold hexRegionCls; rw [if_pos rfl]


theorem hexRegionCls_left (R : HexRegion) {z : ℂ} (hz : z.re = 0)
    (hne : z ≠ R.start) : hexRegionCls R z = 1 := by
  unfold hexRegionCls; rw [if_neg hne, if_pos hz]


theorem hexRegionCls_right (R : HexRegion) {z : ℂ} (hz : z.re = R.width)
    (hne : z ≠ R.start) (hl : z.re ≠ 0) : hexRegionCls R z = 4 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_pos hz]


theorem hexRegionCls_topslant (R : HexRegion) {z : ℂ}
    (hz : Real.sqrt 3 * z.im = R.slant + z.re)
    (hne : z ≠ R.start) (hl : z.re ≠ 0) (hr : z.re ≠ R.width) :
    hexRegionCls R z = 2 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_neg hr, if_pos hz]


theorem hexRegionCls_botslant (R : HexRegion) {z : ℂ}
    (hz : Real.sqrt 3 * z.im = -(R.slant + z.re))
    (hne : z ≠ R.start) (hl : z.re ≠ 0) (hr : z.re ≠ R.width)
    (ht : Real.sqrt 3 * z.im ≠ R.slant + z.re) :
    hexRegionCls R z = 3 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_neg hr, if_neg ht, if_pos hz]


theorem hexRegionCls_eq_one_iff (R : HexRegion) (z : ℂ) :
    hexRegionCls R z = 1 ↔ z.re = 0 ∧ z ≠ R.start := by
  constructor
  · intro h
    unfold hexRegionCls at h
    by_cases h0 : z = R.start
    · rw [if_pos h0] at h; exact absurd h (by decide)
    · rw [if_neg h0] at h
      by_cases h1 : z.re = 0
      · exact ⟨h1, h0⟩
      · rw [if_neg h1] at h
        by_cases h2 : z.re = R.width
        · rw [if_pos h2] at h; exact absurd h (by decide)
        · rw [if_neg h2] at h
          by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
          · rw [if_pos h3] at h; exact absurd h (by decide)
          · rw [if_neg h3] at h
            by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
            · rw [if_pos h4] at h; exact absurd h (by decide)
            · rw [if_neg h4] at h; exact absurd h (by decide)
  · rintro ⟨hz, hne⟩; exact hexRegionCls_left R hz hne


theorem hexRegionCls_eq_four_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 4) : z.re = R.width := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · exact h2
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · rw [if_pos h3] at h; exact absurd h (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · rw [if_pos h4] at h; exact absurd h (by decide)
          · rw [if_neg h4] at h; exact absurd h (by decide)


theorem hexRegionCls_eq_two_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 2) : Real.sqrt 3 * z.im = R.slant + z.re := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · rw [if_pos h2] at h; exact absurd h (by decide)
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · exact h3
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · rw [if_pos h4] at h; exact absurd h (by decide)
          · rw [if_neg h4] at h; exact absurd h (by decide)


theorem hexRegionCls_eq_three_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 3) : Real.sqrt 3 * z.im = -(R.slant + z.re) := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · rw [if_pos h2] at h; exact absurd h (by decide)
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · rw [if_pos h3] at h; exact absurd h (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · exact h4
          · rw [if_neg h4] at h; exact absurd h (by decide)


theorem hexRegionCls_start_eq_zero (R : HexRegion) : hexRegionCls R R.start = 0 :=
  hexRegionCls_start R


end StatMech.Universality
