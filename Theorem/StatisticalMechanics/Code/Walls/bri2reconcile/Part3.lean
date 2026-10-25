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
import Def.StatisticalMechanics.Code.Walls.bri2reconcile.Part3
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bri2_sep_sound {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j₀ j k : Site 2}
    (h : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j₀)).Reachable
          (bgf2_centre L j) (bgf2_centre L k)) :
    ¬ (bkg_deleteVertex (bri2_G ω L) j₀).Reachable j k := by
  intro hr
  exact h (hr.map (bri2_delHom ω L j₀))

end StatMech.Walls
