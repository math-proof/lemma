/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A e = true ↔
      ∀ u v : RlcConnectorVertex n,
        e.1 = s(u, v) → u ∈ A ∧ v ∈ A := by
  classical
  simp [rlc_twoChannelFullPhysicalCutInteriorConfig]


theorem rlc_twoChannelFullPhysicalCutInteriorConfig_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  rintro ⟨x, y, hx, hy, hxy⟩
  obtain ⟨w⟩ := hxy
  obtain ⟨u, v, huv, hu, hv⟩ :=
    rlc_walk_pred_first_exit w (fun z ↦ z ∈ A)
      (hAright x hx) (hAleft y hy)
  have hopen := w.adj_of_mem_edges huv
  rw [FK.openSub_adj] at hopen
  have hextend : rlc_twoChannelEdgeConfigExtend gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
      s(u, v) = rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
        ⟨s(u, v), hopen.1⟩ := by
    simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
      hopen.1]
  have htrue : rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
      ⟨s(u, v), hopen.1⟩ = true := by
    rw [← hextend]
    exact hopen.2
  have hends :=
    (rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff gamma gamma' A
      ⟨s(u, v), hopen.1⟩).mp htrue u v rfl
  exact hv hends.2


end
end StatMech.Universality
