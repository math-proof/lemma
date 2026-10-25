/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Def.StatisticalMechanics.Code.Walls.wadangledefect.Part4
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

theorem wad_defectSum_eq_counts (K : Finset Cell) :
    ∑ v ∈ regVerts K, defect K v = wad_n1 K - wad_n3 K - 2 * wad_n2d K := by
  classical
  unfold wad_n1 wad_n3 wad_n2d
  
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rcases wad_defect_classify K v hv with h | h | h | h <;> rw [h] <;> norm_num


theorem wad_defect_eq_four_chi_counts (K : Finset Cell) :
    wad_n1 K - wad_n3 K - 2 * wad_n2d K = 4 * regChi K := by
  rw [← wad_defectSum_eq_counts, wad_defect_eq_four_chi]


theorem wad_defect_eq_four {K : Finset Cell} (hK : EucBuildable K) (hpinch : wad_n2d K = 0) :
    wad_n1 K - wad_n3 K = 4 := by
  have h := wad_defect_eq_four_chi_counts K
  rw [hpinch, euc_chi_induction hK] at h
  linarith


theorem wad_n1_unitSquare : wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 := by
  unfold wad_n1; decide

theorem wad_n3_unitSquare : wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
  unfold wad_n3; decide

theorem wad_n2d_unitSquare : wad_n2d ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_unitSquare :
    wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 :=
  wad_defect_eq_four (EucBuildable.singleton _) wad_n2d_unitSquare


theorem wad_n2d_domino : wad_n2d ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_domino :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 4 :=
  wad_defect_eq_four euc_buildable_domino wad_n2d_domino


theorem wad_n1_Ltromino : wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 5 := by
  unfold wad_n1; decide

theorem wad_n3_Ltromino : wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 1 := by
  unfold wad_n3; decide

theorem wad_n2d_Ltromino : wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_Ltromino :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 4 :=
  wad_defect_eq_four euc_buildable_Ltromino wad_n2d_Ltromino


theorem wad_witness_holeyRing :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      - 2 * wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      = 0 := by
  rw [wad_defect_eq_four_chi_counts, euc_chi_holeyRing]; ring

end StatMech.Wad
