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
import Def.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part4
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bgf2_indexAllOpen_connected {L : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} {j : Site 2}
    (h : bgf2_IndexAllOpen ω L j) {a b : Site 2} (ha : bgn_idx L a = j) (hb : bgn_idx L b = j) :
    Connected 2 ω a b := by
  refine bgf2_boxCentre_connected (L := L) (c := bgf2_centre L j) ?_ ?_ ?_
  · intro x y hx hy hadj
    exact h x y (bgf2_idx_iff_inBox.mpr hx) (bgf2_idx_iff_inBox.mpr hy) hadj
  · exact bgf2_idx_iff_inBox.mp ha
  · exact bgf2_idx_iff_inBox.mp hb

#check @bgf2_indexAllOpen_connected


end StatMech.Walls
