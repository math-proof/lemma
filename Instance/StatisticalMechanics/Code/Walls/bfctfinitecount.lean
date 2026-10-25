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
import Def.StatisticalMechanics.Code.Walls.bfctfinitecount
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

instance bfct_restrict_decAdj {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (bfct_restrict G S).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj (a : V) (b : V)))

end StatMech.Walls
