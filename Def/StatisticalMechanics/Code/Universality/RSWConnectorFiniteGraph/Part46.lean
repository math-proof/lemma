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
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part32
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

noncomputable def rlc_connectorOuterComponentMap {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).ConnectedComponent →
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent :=
  ConnectedComponent.lift
    (fun x => (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).connectedComponentMk
          (rlc_connectorOuterFaceProjection gamma gamma' x))
    (fun _ _ p _ => ConnectedComponent.sound
      (rlc_connectorOuterFaceProjection_reachable gamma gamma' tau
        p.reachable))

end
end StatMech.Universality
