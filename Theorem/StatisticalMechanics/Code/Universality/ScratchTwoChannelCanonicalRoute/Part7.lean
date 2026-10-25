/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelPIMSConfig_variableTarget_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) target.1.1 =
      !(omega (rlc_twoChannelPIMSSourceEdge target)) := by
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) target.2]
  have hlift : rlc_connectorCentralFaceEdgeLift
      (rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)) target.2 =
        (rlc_twoChannelPIMSSourceEdge target).1 := by
    rfl
  rw [hlift]
  have hedge := (rlc_twoChannelPIMSSourceEdge target).2
  simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
    hedge]


theorem rlc_twoChannel_PIMS_and_exactDiscardedBits_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_connectorCentralFacePIMSConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega),
        fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  change rlc_connectorCentralFacePIMSConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' rho) =
    rlc_connectorCentralFacePIMSConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' sigma) at hpims
  change (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      rho e.1) =
    (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      sigma e.1) at hdiscarded
  funext e
  by_cases hvisible : e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, rfl⟩ := hvisible
    have happ := congrFun hpims target.1.1
    rw [rlc_twoChannelPIMSConfig_variableTarget_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply] at happ
    have hdouble := congrArg (fun b : Bool => !b) happ
    simpa using hdouble
  · let discarded : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' :=
      ⟨e, hvisible⟩
    exact congrFun hdiscarded discarded


end
end StatMech.Universality
