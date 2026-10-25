/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part32
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorCollaredOuterDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')) :=
  fun e => if h : ∃ f,
      rlc_connectorCollaredOuterDualEdge gamma gamma' f = e then
    !(rlc_connectorForceTraceConfig gamma gamma' tau h.choose.1)
  else decide
    (e ∈ (rlc_connectorCollaredOuterSpokeGraph gamma gamma').edgeSet)


noncomputable def rlc_connectorCollaredDualEnds {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Sym2 (Ising.kwg_Face
      (rlc_connectorCollaredPlanarDomain gamma gamma')) :=
  s(BeffaraDC.pfdFace (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f),
    BeffaraDC.pfdFace (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f))


end
end StatMech.Universality
