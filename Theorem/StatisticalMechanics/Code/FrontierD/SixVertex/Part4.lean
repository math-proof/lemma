/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part5
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexTransfer_apply (N : ℕ) (c : ℝ) (x y : SixVertexRow N) :
    sixVertexTransfer N c x y =
      if x = y then 2
      else if SixVertexInterlaced x y then c ^ sixVertexRowDistance x y else 0 :=
  rfl

theorem sixVertexTransfer_symmetric (N : ℕ) (c : ℝ) (x y : SixVertexRow N) :
    sixVertexTransfer N c x y = sixVertexTransfer N c y x := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  · have hyx : y ≠ x := Ne.symm hxy
    by_cases hi : SixVertexInterlaced x y
    · have hi' : SixVertexInterlaced y x := (sixVertexInterlaced_comm x y).1 hi
      simp [sixVertexTransfer, hxy, hyx, hi, hi', sixVertexRowDistance_comm]
    · have hi' : ¬ SixVertexInterlaced y x := by
        simpa only [sixVertexInterlaced_comm] using hi
      simp [sixVertexTransfer, hxy, hyx, hi, hi']


theorem sixVertexTransfer_eq_zero_of_upCount_ne {N : ℕ} (c : ℝ)
    {x y : SixVertexRow N} (hxy : sixVertexUpCount x ≠ sixVertexUpCount y) :
    sixVertexTransfer N c x y = 0 := by
  classical
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  have hinter : ¬ SixVertexInterlaced x y :=
    fun h => hxy (sixVertexInterlaced_upCount_eq h)
  simp [sixVertexTransfer, hne, hinter]


theorem sixVertexTransfer_preserves_upCount {N : ℕ} (c : ℝ)
    {x y : SixVertexRow N} (h : sixVertexTransfer N c x y ≠ 0) :
    sixVertexUpCount x = sixVertexUpCount y := by
  by_contra hne
  exact h (sixVertexTransfer_eq_zero_of_upCount_ne c hne)

theorem sixVertexTransfer_nonneg {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x y : SixVertexRow N) : 0 ≤ sixVertexTransfer N c x y := by
  classical
  simp only [sixVertexTransfer]
  split_ifs
  · norm_num
  · positivity
  · exact le_rfl


end StatMech.FrontierD
