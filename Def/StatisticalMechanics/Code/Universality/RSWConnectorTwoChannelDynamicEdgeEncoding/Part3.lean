/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def RlcTwoChannelEdgeCodeHall {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop) : Prop := by
  classical
  exact ∀ failures : Finset (RlcTwoChannelEdgeFailure gamma gamma'),
      failures.card <=
        (Finset.univ.filter fun eta : RlcTwoChannelEdgeSuccess gamma gamma' =>
          ∃ rho ∈ failures, Compatible rho eta).card


end
end StatMech.Universality
