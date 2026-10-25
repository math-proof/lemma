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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorTraceFibreCondEventMass_eq_forcedTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorTraceFibreCondEventMass gamma gamma' p q =
      rlc_connectorForcedTraceActiveEventMass gamma gamma' p q := by
  unfold rlc_connectorTraceFibreCondEventMass
    rlc_connectorForcedTraceActiveEventMass
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorTraceFibre_condBcProb_eq]


theorem rlc_connectorTraceFibreCondEventMass_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorTraceFibreCondEventMass gamma gamma' p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  rw [rlc_connectorTraceFibreCondEventMass_eq_forcedTrace,
    rlc_connectorForcedTraceActiveEventMass_eq_separate
      gamma gamma' hp hp1 hq]


theorem rlc_connectorTraceFibreCondEventMass_selfDual_ge_one_div_one_add_q
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      rlc_connectorTraceFibreCondEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [rlc_connectorTraceFibreCondEventMass_eq_separate
    gamma gamma' hp hp1 hq0]
  exact rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq hdual


end
end StatMech.Universality
