/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullIndexedOuterState {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')) :=
  FK.ocd_outProj (rlc_twoChannelFullInnerOuterVertex gamma gamma')
    (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)


def RlcTwoChannelFullIndexedFibreSupported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))) : Prop :=
  ∃ omega : RlcTwoChannelEdgeConfig gamma gamma',
    psi = rlc_twoChannelFullIndexedOuterState gamma gamma' omega

end
end StatMech.Universality
