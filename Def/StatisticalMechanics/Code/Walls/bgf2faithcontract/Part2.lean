/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


def bgf2_AllOpenAt (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (c : Site 2) : Prop :=
  ∀ x y : Site 2, bgf2_inBox L c x → bgf2_inBox L c y → (hypercubicLattice 2).Adj x y →
    ω s(x, y) = true


end StatMech.Walls
