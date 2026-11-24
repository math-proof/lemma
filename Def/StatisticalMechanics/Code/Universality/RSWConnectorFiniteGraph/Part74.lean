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
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part55
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

noncomputable def rlc_connectorCollaredOuterFaceProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorCollaredOuterVertex gamma gamma' →
      Ising.kwg_Face (rlc_connectorCollaredPlanarDomain gamma gamma')
  | Sum.inl x => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
  | Sum.inr (Sum.inl (f, false)) => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inl (f, true)) => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inr C) => C

def RlcConnectorCollaredOuterIsFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorCollaredOuterVertex gamma gamma' → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

end
end StatMech.Universality
