/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelAmbientSourceEdge_unique {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {e : Sym2 (Site 2)}
    (f g : RlcTwoChannelAmbientSourceEdge gamma gamma' e) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (f.2.trans g.2.symm)


end
end StatMech.Universality
