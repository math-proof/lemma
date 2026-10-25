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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorForcedTraceActiveWeight_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
  rw [rlc_connectorForcedTraceActiveWeight,
    rlc_fkWeight_augmented_forceTrace_eq_separateBC]
  rfl


theorem rlc_connectorForcedTraceActiveZ_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorForcedTraceActiveZ gamma gamma' p q =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q := by
  unfold rlc_connectorForcedTraceActiveZ
  simp_rw [rlc_connectorForcedTraceActiveWeight_eq_separate]
  rw [← Finset.mul_sum]
  rfl


theorem rlc_connectorForcedTraceActiveProb_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForcedTraceActiveProb gamma gamma' p q eta =
      FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
  unfold rlc_connectorForcedTraceActiveProb FK.activeBCProb
  rw [rlc_connectorForcedTraceActiveWeight_eq_separate,
    rlc_connectorForcedTraceActiveZ_eq_separate]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hp.ne')


end
end StatMech.Universality
