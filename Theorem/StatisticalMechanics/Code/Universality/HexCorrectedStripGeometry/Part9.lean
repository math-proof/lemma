/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part9


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexCSCanonicalHeading_unit {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexUnit (hexCSCanonicalHeading e) =
      hexUnit (hexAWHeading e.vtx.1 e.edge) := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge
  · change hexUnit (if 0 ≤ i - j then 4 else -2) = hexUnit 4
    split
    · rfl
    · rw [show (4 : ℤ) = -2 + 6 by norm_num, hexUnit_add_six]
  · change hexUnit 0 = hexUnit 0
    rfl
  · change hexUnit 2 = hexUnit 2
    rfl
  · change hexUnit 1 = hexUnit 7
    rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]
  · change hexUnit 3 = hexUnit 3
    rfl
  · change hexUnit (-1) = hexUnit 5
    rw [show (5 : ℤ) = -1 + 6 by norm_num, hexUnit_add_six]


theorem hexCSCanonicalHeading_reflect {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexCSCanonicalHeading (hexCSReflectIncidence e) =
      2 - hexCSCanonicalHeading e := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge
  · have hraw : -j + -i = 0 := by
      simpa [hexAWDepth, hexAWLong] using hb
    have hsum : i + j = 0 := by omega
    have htrans : i - j ≠ 0 := by
      intro ht
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      apply hne
      rw [HexIncidence.mk.injEq]
      constructor
      · apply Subtype.ext
        simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord, hi, hj]
      · rfl
    change (if 0 ≤ j - i then 4 else -2) =
      2 - (if 0 ≤ i - j then 4 else -2)
    by_cases hsign : 0 ≤ i - j
    · have hji : j ≤ i := by omega
      have hnij : ¬ i ≤ j := by omega
      simp [hji, hnij]
    · have hij : i ≤ j := by omega
      have hnji : ¬ j ≤ i := by omega
      simp [hij, hnji]
  · exfalso
    simpa [hexAWDepth, hexAWLong] using hb
  · exfalso
    simpa [hexAWDepth, hexAWLong] using hb
  · change (1 : ℤ) = 2 - 1
    omega
  · change (-1 : ℤ) = 2 - 3
    omega
  · change (3 : ℤ) = 2 - (-1)
    omega


end
end StatMech.Universality
