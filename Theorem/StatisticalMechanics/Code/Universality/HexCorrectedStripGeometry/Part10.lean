/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part10


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexCS_boundary_cosine {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    Real.cos (hexPhase_sideTilt (hexCSCanonicalHeading e) +
        (5 / 8 : ℝ) * hexCSCanonicalWinding e) =
      match hexCSBoundaryClass e with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1 := by
  obtain h | h | h | h := hexCS_boundary_classification e he
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalWinding, hexCSCanonicalHeading,
      hexCSBoundaryClass, hc, hedge, hexPhase_sideTilt, hexCl]
    split
    · norm_num
      have hang : -(3 * (Real.pi / 3)) + (5 / 8 : ℝ) * Real.pi =
          -(3 * Real.pi / 8) := by ring
      rw [hang, Real.cos_neg]
    · norm_num
      have hang : 3 * (Real.pi / 3) + -((5 / 8 : ℝ) * Real.pi) =
          3 * Real.pi / 8 := by ring
      rw [hang]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hc, hedge]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hexCt, hc, hedge]
    norm_num
    have hang : -(2 * (Real.pi / 3)) +
        (5 / 8 : ℝ) * (Real.pi / 3 * 2) = -(Real.pi / 4) := by ring
    rw [hang, Real.cos_neg, Real.cos_pi_div_four]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hexCt, hc, hedge]
    norm_num
    have hang : 2 * (Real.pi / 3) +
        -((5 / 8 : ℝ) * (Real.pi / 3 * 2)) = Real.pi / 4 := by ring
    rw [hang, Real.cos_pi_div_four]


end
end StatMech.Universality
