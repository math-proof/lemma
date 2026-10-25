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
import Theorem.StatisticalMechanics.Code.Walls.bri2reconcile.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

def bri2_delHom (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j₀ : Site 2) :
    bkg_deleteVertex (bri2_G ω L) j₀ →g bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j₀) where
  toFun := bgf2_centre L
  map_rel' := by
    rintro p q ⟨hadj, hp, hq⟩
    exact ⟨hadj, fun h => hp (bgf2_centre_inj h), fun h => hq (bgf2_centre_inj h)⟩


end StatMech.Walls
