/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable instance rlc_twoChannelFullPhysicalTargetEdgeDecidable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (fun target :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet =>
        Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :=
  Classical.decPred _


end
end StatMech.Universality
