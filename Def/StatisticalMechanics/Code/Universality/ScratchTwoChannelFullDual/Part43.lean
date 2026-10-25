/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullIndexed_actualConnectorFibreMass
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (p q : Real)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Real :=
  ∑ rho,
    (FK.ocd_innerRestrict
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹'
        rlc_twoChannelFullInnerExteriorEvent gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
      FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) rho

end
end StatMech.Universality
