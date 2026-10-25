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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_numClustersBC_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') tau =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') tau := by
  unfold FK.numClustersBC
  exact Nat.card_congr (rlc_connectorTraceComponentEquiv gamma gamma'
    (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau))


theorem rlc_bcWeight_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q tau =
      FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.bcWeight
  rw [rlc_numClustersBC_traceWiring_eq_separateWiring]


theorem rlc_bcZ_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q =
      FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
  unfold FK.bcZ
  apply Finset.sum_congr rfl
  intro tau _
  exact rlc_bcWeight_traceWiring_eq_separateWiring gamma gamma' p q tau


theorem rlc_bcProb_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q tau =
      FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.bcProb
  rw [rlc_bcWeight_traceWiring_eq_separateWiring,
    rlc_bcZ_traceWiring_eq_separateWiring]


theorem rlc_bcEventMass_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_traceWiring_eq_separateWiring]


end
end StatMech.Universality
