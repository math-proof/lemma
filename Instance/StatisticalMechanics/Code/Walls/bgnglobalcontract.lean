/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Def.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


instance : DecidableRel bgn_W.Adj := by
  unfold bgn_W; infer_instance

instance bgn_deleteVertex_decidable {V : Type*} [DecidableEq V] (Amb : SimpleGraph V)
    [DecidableRel Amb.Adj] (t : V) : DecidableRel (bkg_deleteVertex Amb t).Adj :=
  fun a b => decidable_of_iff _ (bkg_deleteVertex_adj Amb t a b).symm


end StatMech.Walls
