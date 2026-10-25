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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part46
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorOuterComponentMap_mk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterComponentMap gamma gamma' tau
        ((rlc_connectorOuterOpenGraph gamma gamma' tau).connectedComponentMk x) =
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).connectedComponentMk
        (rlc_connectorOuterFaceProjection gamma gamma' x) :=
  rfl

theorem rlc_connectorOuterComponentMap_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Function.Injective
      (rlc_connectorOuterComponentMap gamma gamma' tau) := by
  intro A B hAB
  induction A using ConnectedComponent.ind with
  | _ x =>
    induction B using ConnectedComponent.ind with
    | _ y =>
      rw [rlc_connectorOuterComponentMap_mk,
        rlc_connectorOuterComponentMap_mk, ConnectedComponent.eq] at hAB
      exact ConnectedComponent.sound
        ((rlc_connectorOuter_reachable_iff_pfd gamma gamma' tau x y).2 hAB)

theorem rlc_connectorOuterComponentMap_surjective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Function.Surjective
      (rlc_connectorOuterComponentMap gamma gamma' tau) := by
  intro C
  induction C using ConnectedComponent.ind with
  | _ c =>
    refine ⟨(rlc_connectorOuterOpenGraph gamma gamma' tau).connectedComponentMk
      (rlc_connectorOuterFace gamma gamma' c), ?_⟩
    rw [rlc_connectorOuterComponentMap_mk]
    rfl


end
end StatMech.Universality
