module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part7
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcConnectorPIMSExteriorTraceLocal {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ ⦃x y : RlcConnectorVertex n⦄,
    (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y →
      (rlc_connectorOnRight gamma x ∧ rlc_connectorOnRight gamma y) ∨
      (rlc_connectorOnLeft gamma' x ∧ rlc_connectorOnLeft gamma' y)


def RlcConnectorPIMSExtremalSelectionExteriorLocality (n : Int) : Prop :=
  ∀ pair : RlcDiagonalPathPair n,
    (rlc_extremalPairCandidate pair).Nonempty →
      RlcConnectorPIMSExteriorTraceLocal pair.1 pair.2


end
end StatMech.Universality
