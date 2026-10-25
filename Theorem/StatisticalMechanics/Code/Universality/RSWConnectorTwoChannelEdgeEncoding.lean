/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part9
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelEdgeConfigCombine_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside e.1 =
      omega e := by
  simp [rlc_twoChannelEdgeConfigCombine, rlc_twoChannelConfigSplitEquiv,
    e.2]

theorem rlc_openSub_twoChannel_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have he : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    simpa [rlc_twoChannelEdgeConfigCombine,
      rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv, he]
      using hopen
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have he : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    simpa [rlc_twoChannelEdgeConfigCombine,
      rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv, he]
      using hopen

theorem rlc_twoChannel_edgeConfigCombine_mem_event_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  change (∃ x y, rlc_connectorOnRight gamma x ∧
      rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside)).Reachable x y) ↔
    ∃ x y, rlc_connectorOnRight gamma x ∧
      rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)).Reachable x y
  rw [rlc_openSub_twoChannel_edgeConfigCombine]


theorem rlc_twoChannel_split_fst_mem_event_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
          ((rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1) ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  have hrho : rlc_twoChannelEdgeConfigCombine gamma gamma'
      (split rho).1 (split rho).2 = rho := split.symm_apply_apply rho
  constructor
  · intro hedge
    have hcombine := (rlc_twoChannel_edgeConfigCombine_mem_event_iff
      gamma gamma' (split rho).1 (split rho).2).mpr hedge
    simpa only [hrho] using hcombine
  · intro hfull
    apply (rlc_twoChannel_edgeConfigCombine_mem_event_iff
      gamma gamma' (split rho).1 (split rho).2).mp
    simpa only [hrho] using hfull


end
end StatMech.Universality
