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
public import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part25
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

def rlc_connectorInnerEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :=
  {omega | (FK.openSub (rlc_connectorInnerGraph gamma gamma') omega ⊔
      rlc_connectorInnerSeparateWiring gamma gamma').Reachable
        (rlc_connectorInnerRightAnchor gamma gamma')
        (rlc_connectorInnerLeftAnchor gamma gamma')}


noncomputable def rlc_connectorInnerInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  FK.ocd_inducedWiring (rlc_connectorOuterDualGraph gamma gamma')
    (rlc_connectorInnerOuterVertex gamma gamma') (fun _ => False) psi

end
end StatMech.Universality
