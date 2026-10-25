/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

def bfct_delHom {V : Type*} (G : SimpleGraph V) (S : Finset V) (t : {v // v ∈ S}) :
    bkg_deleteVertex (bfct_restrict G S) t →g bkg_deleteVertex G (t : V) :=
  { toFun := Subtype.val
    map_rel' := by
      rintro a b ⟨hadj, hat, hbt⟩
      exact ⟨hadj, fun h => hat (Subtype.ext h), fun h => hbt (Subtype.ext h)⟩ }


end StatMech.Walls
