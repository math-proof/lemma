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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau = ⊥ := by
  ext x y
  rw [rlc_connectorPIMSCollaredExteriorOpenGraph, FK.openSub_adj]
  constructor
  · rintro ⟨hclass, hopen⟩
    rcases hclass with htrace | hext
    · have hclosed :=
        rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
          gamma gamma' tau s(x, y) htrace.2
      exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
    · have hclosed :=
        rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
          gamma gamma' tau s(x, y) hext.1.2 hext.2.1 hext.2.2
      exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · intro hbot
    exact hbot.elim


theorem rlc_connectorPIMSCollaredExterior_oneAttachment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    RlcConnectorExteriorOneAttachment
      (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) := by
  intro x y hxy
  rw [rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot] at hxy
  exact SimpleGraph.reachable_bot.mp hxy


theorem rlc_connectorPIMSCollaredInducedWiring_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) = ⊥ :=
  rlc_connectorComponentWiring_eq_bot_of_oneAttachment _
      (rlc_connectorPIMSCollaredExterior_oneAttachment gamma gamma' tau)


end
end StatMech.Universality
