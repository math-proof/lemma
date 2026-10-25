/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Def.StatisticalMechanics.Code.Walls.bri2reconcile.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bri2_faithful_sound {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j k : Site 2}
    (h : (bri2_G ω L).Reachable j k) :
    Connected 2 ω (bgf2_centre L j) (bgf2_centre L k) := by
  have hGf : (bgf2_Gf ω L).Reachable (bgf2_centre L j) (bgf2_centre L k) := h.map (bri2_hom ω L)
  have hf := bgf2_faithful ω L (bgf2_centre L j) (bgf2_centre L k)
  rw [bri2_q_centre, bri2_q_centre] at hf
  exact hf.mp hGf


end StatMech.Walls
