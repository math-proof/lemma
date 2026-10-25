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
import Def.StatisticalMechanics.Code.Walls.bfctfinitecount.Part3
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

instance : DecidableRel bfct_star.Adj := by unfold bfct_star; infer_instance

instance bfct_delDec {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : V) :
    DecidableRel (bkg_deleteVertex G t).Adj :=
  fun a b => decidable_of_iff _ (bkg_deleteVertex_adj G t a b).symm


end StatMech.Walls
