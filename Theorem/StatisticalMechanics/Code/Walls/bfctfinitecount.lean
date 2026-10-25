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
import Instance.StatisticalMechanics.Code.Walls.bfctfinitecount
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

@[simp] theorem bfct_restrict_adj {V : Type*} (G : SimpleGraph V) (S : Finset V)
    (a b : {v // v ∈ S}) : (bfct_restrict G S).Adj a b ↔ G.Adj (a : V) (b : V) :=
  Iff.rfl

#check @bfct_restrict


end StatMech.Walls
