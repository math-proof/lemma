/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part33
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullIndexedOuterState_supported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    RlcTwoChannelFullIndexedFibreSupported gamma gamma'
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) :=
  ⟨omega, rfl⟩

theorem rlc_twoChannelFullIndexedOuterState_fixed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_outProj (rlc_twoChannelFullInnerOuterVertex gamma gamma')
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) =
      rlc_twoChannelFullIndexedOuterState gamma gamma' omega := by
  exact FK.ocd_outProj_idem
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _


theorem rlc_twoChannelFullIndexedOuterState_eq_of_discarded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega omega' : RlcTwoChannelEdgeConfig gamma gamma')
    (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma',
      omega e.1 = omega' e.1) :
    rlc_twoChannelFullIndexedOuterState gamma gamma' omega =
      rlc_twoChannelFullIndexedOuterState gamma gamma' omega' := by
  have hagree := rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded
    gamma gamma' omega omega' hdiscarded
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm


end
end StatMech.Universality
