/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullInnerInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') :=
  FK.ocd_inducedWiring (rlc_twoChannelIndexedOuterGraph gamma gamma')
    (rlc_twoChannelFullInnerOuterVertex gamma gamma')
    (fun _ => False) psi

end
end StatMech.Universality
