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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part29
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_pimsEdgeEquiv_connectorReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_pimsEdgeEquiv
        (rlc_connectorReflectedDualEdge gamma gamma' f) =
      Ising.kwg_embeddedEdge
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
  rw [rlc_connectorReflectedDualEdge,
    rlc_pimsEdgeEquiv_reflected_mk_of_adj
      (Ising.kwg_flanks_adj _ f), Ising.kwg_flanks_shared]


theorem rlc_connectorReflectedDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorReflectedDualEdge gamma gamma') := by
  intro e f hef
  have hemb := congrArg rlc_pimsEdgeEquiv hef
  simp only [rlc_pimsEdgeEquiv_connectorReflectedDualEdge] at hemb
  apply Subtype.ext
  apply rlc_sym2Map_subtypeVal_injective
  simpa [Ising.kwg_embeddedEdge,
    rlc_connectorAugmentedPlanarDomain] using hemb


end
end StatMech.Universality
