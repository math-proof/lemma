/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullDual_mem_event_iff_variableExterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullDualConfig gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rlc_twoChannelFullVariableProjection gamma gamma' omega ∈
        rlc_twoChannelFullVariableExteriorEvent gamma gamma' := by
  have hvariable : FK.openSub
      (rlc_twoChannelFullVariableGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega) =
      FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
        (FK.extendActive (rlc_twoChannelFullVariableGraph gamma gamma')
          (rlc_twoChannelFullVariableProjection gamma gamma' omega)) := by
    ext x y
    simp only [FK.openSub_adj]
    constructor <;> rintro ⟨hxy, hopen⟩ <;> refine ⟨hxy, ?_⟩
    · have he : s(x, y) ∈
          (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy
      simpa [FK.extendActive, rlc_twoChannelFullVariableProjection, he]
        using hopen
    · have he : s(x, y) ∈
          (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy
      simpa [FK.extendActive, rlc_twoChannelFullVariableProjection, he]
        using hopen
  unfold rlc_finiteTwoChannelConnectorEvent
    rlc_twoChannelFullVariableExteriorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior,
    hvariable]


end
end StatMech.Universality
