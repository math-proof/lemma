/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part3
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bgf2_idx_iff_inBox {L : ℕ} {j x : Site 2} :
    bgn_idx L x = j ↔ bgf2_inBox L (bgf2_centre L j) x := by
  constructor
  · intro h i
    have hxi : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i := by rw [← h]; rfl
    have h2 := (bsc_ediv_eq_iff).mp hxi
    simpa [bgf2_centre] using h2
  · intro h; funext i
    show (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i
    refine (bsc_ediv_eq_iff).mpr ?_
    have := h i
    simpa [bgf2_centre] using this


theorem bgf2_idx_centre (L : ℕ) (j : Site 2) : bgn_idx L (bgf2_centre L j) = j :=
  bgf2_idx_iff_inBox.mpr (by intro i; simp [bgf2_centre])


theorem bgf2_centre_inj {L : ℕ} {j k : Site 2} (h : bgf2_centre L j = bgf2_centre L k) : j = k := by
  funext i
  have := congrFun h i
  simp only [bgf2_centre] at this
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hb this


end StatMech.Walls
