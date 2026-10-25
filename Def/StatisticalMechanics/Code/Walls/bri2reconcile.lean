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
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

def bri2_G (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : SimpleGraph (Site 2) :=
  SimpleGraph.comap (bgf2_centre L) (bgf2_Gf ω L)

end StatMech.Walls
