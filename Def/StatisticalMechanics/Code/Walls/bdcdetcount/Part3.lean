/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bsgspantreegn
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

def bdc_delHom (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2) :
    bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j) →g
      bkg_deleteVertex (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L) 0 where
  toFun p := p - bgf2_centre L j
  map_rel' := by
    rintro p q ⟨hadj, hp, hq⟩
    refine ⟨?_, sub_ne_zero.mpr hp, sub_ne_zero.mpr hq⟩
    rw [bdc_Gf_shift_adj, sub_add_cancel, sub_add_cancel]; exact hadj


end StatMech.Walls
