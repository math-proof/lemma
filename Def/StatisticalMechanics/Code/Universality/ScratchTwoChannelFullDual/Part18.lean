/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelIndexedOuterPort {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (side : Bool) : RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  Sum.inr (Sum.inl (f, side))

def rlc_twoChannelIndexedOuterFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  Sum.inr (Sum.inr C)

def RlcTwoChannelIndexedRetainedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) : Prop :=
  ∃ e : RlcTwoChannelFullVariableTargetEdge gamma gamma',
    e.1.map Subtype.val = rlc_twoChannelReflectedDualEdge gamma gamma' f

end
end StatMech.Universality
