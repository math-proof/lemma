/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral
open Set SimpleGraph Finset


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


def bgfdCentre (L : ℕ) (j : Site d) : Site d :=
  fun i => (2 * (L : ℤ) + 1) * j i


end StatMech.FrontierA
