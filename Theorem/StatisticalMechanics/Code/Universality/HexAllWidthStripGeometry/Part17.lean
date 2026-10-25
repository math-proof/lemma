/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAW_fixed_boundary_classification {T L : ℕ}
    (e : HexAWIncidence T L)
    (heBoundary : e ∈ hexAWBoundaryIncidences T L)
    (heFixed : hexAWReflectIncidence e = e) :
    (e.vtx.1 = hexAWOriginCoord ∧ e.edge = 0) ∨
      ∃ k : ℕ, T = 2 * k ∧
        e.vtx.1 = hexAWRightFixedCoord k ∧ e.edge = 0 := by
  obtain ⟨hij, he0⟩ := hexAWReflectIncidence_fixed_shape e heFixed
  have hc : hexAWInStrip T L e.vtx.1 :=
    (hexAW_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hn : ¬ hexAWInStrip T L (hexAWNeighbor e.vtx.1 e.edge) := by
    rw [hexAW_mem_boundary_iff] at heBoundary
    unfold hexAWIsInterior at heBoundary
    rwa [hexAW_mem_vertexSet_iff] at heBoundary
  rcases hcoord : e.vtx.1 with ⟨i, j, color⟩
  have hij' : i = j := by
    simpa [hcoord] using hij
  subst j
  rw [hcoord] at hc
  rw [hcoord, he0] at hn
  cases color with
  | black =>
      have hi : i = 0 := by
        by_contra hi0
        apply hn
        simp only [hexAWNeighbor, hexAWInStrip, hexAWBookRe2,
          hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
        simp only [hexAWInStrip, hexAWBookRe2, hexAWBookSqrt3Im2,
          hexAWDepth, hexAWLong, hexAWTrans] at hc
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      left
      refine ⟨?_, he0⟩
      rw [hi]
      rfl
  | white =>
      have hright : (T : ℤ) = -2 * i := by
        have houtside :
            ¬ hexAWInStrip T L
              ⟨i, i, HexAWColor.black⟩ := by
          simpa [hexAWNeighbor] using hn
        simp only [hexAWInStrip, hexAWBookRe2,
          hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
          hexAWTrans] at hc
        have htooFar : (3 * T : ℕ) < -6 * i + 1 := by
          by_contra hle
          apply houtside
          simp only [hexAWInStrip, hexAWBookRe2,
            hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
            hexAWTrans]
          constructor
          · omega
          constructor
          · omega
          constructor <;> omega
        omega
      let k : ℕ := Int.toNat (-i)
      have hki : (k : ℤ) = -i := by
        exact Int.toNat_of_nonneg (by
          simp only [hexAWInStrip, hexAWBookRe2,
            hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
            hexAWTrans] at hc
          omega)
      right
      refine ⟨k, ?_, ?_, he0⟩
      · have hTk : (T : ℤ) = ((2 * k : ℕ) : ℤ) := by
          rw [hright]
          push_cast
          rw [hki]
          ring
        exact_mod_cast hTk
      · have hik : i = -(k : ℤ) := by omega
        rw [hik]
        rfl


@[simp] theorem hexAWRightFixedCoord_mem (k L : ℕ) (hk : 0 < k) :
    hexAWRightFixedCoord k ∈ hexAWVertexSet (2 * k) L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWRightFixedCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega


end
end StatMech.Universality
