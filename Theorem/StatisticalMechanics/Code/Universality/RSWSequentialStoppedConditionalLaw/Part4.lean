/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorTraceFibre_bcWeight_bot_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.bcWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
      rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta := by
  change FK.edgeProduct
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorTraceFibreConfig gamma gamma' eta) *
      q ^ FK.numClustersBC
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n))
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
    FK.edgeProduct (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorTraceFibreConfig gamma gamma' eta) *
      q ^ FK.numClusters
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta)
  rw [FK.numClustersBC]
  have hbot : FK.openSub
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta) ⊔
      (⊥ : SimpleGraph (RlcConnectorVertex n)) =
      FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta) := by
    ext x y
    simp
  rw [hbot, FK.numClusters, Nat.card_eq_fintype_card]

set_option maxHeartbeats 800000 in


theorem rlc_connectorTraceFibre_inducedBcZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.inducedBcZ (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreInside gamma gamma')
        (rlc_connectorTraceFibreReference gamma gamma') =
      rlc_connectorForcedTraceActiveZ gamma gamma' p q := by
  unfold FK.inducedBcZ rlc_connectorForcedTraceActiveZ
  let S := FK.condFibre (rlc_connectorTraceFibreInside gamma gamma')
    (rlc_connectorTraceFibreReference gamma gamma')
  let weight := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    FK.bcWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G
      (⊥ : SimpleGraph (RlcConnectorVertex n)) p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((rlc_connectorTraceFibreEquiv gamma gamma') eta) :=
      (Equiv.sum_comp (rlc_connectorTraceFibreEquiv gamma gamma')
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, rlc_connectorForcedTraceActiveWeight
        gamma gamma' p q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact rlc_connectorTraceFibre_bcWeight_bot_eq gamma gamma' p q eta


theorem rlc_connectorTraceFibre_condBcProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.condBcProb (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreInside gamma gamma')
        (rlc_connectorTraceFibreReference gamma gamma')
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
      rlc_connectorForcedTraceActiveProb gamma gamma' p q eta := by
  unfold FK.condBcProb
  split
  · rw [rlc_connectorTraceFibre_inducedBcZ_eq]
    rw [rlc_connectorTraceFibre_bcWeight_bot_eq]
    rfl
  · rename_i h
    exact (h (rlc_connectorTraceFibreConfig_agreesOff gamma gamma' eta)).elim


end
end StatMech.Universality
