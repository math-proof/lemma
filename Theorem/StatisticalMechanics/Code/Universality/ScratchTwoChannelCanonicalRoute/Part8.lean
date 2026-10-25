/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelPIMSEdgeProjection_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e =
      rlc_connectorCentralFacePIMSConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) e.1 := by
  rfl


theorem rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_twoChannelPIMSEdgeProjection gamma gamma' omega,
        fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  change rlc_twoChannelPIMSEdgeProjection gamma gamma' rho =
    rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma at hpims
  change (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      rho e.1) =
    (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      sigma e.1) at hdiscarded
  funext e
  by_cases hvisible : e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, rfl⟩ := hvisible
    have happ := congrFun hpims target.1
    rw [rlc_twoChannelPIMSEdgeProjection_apply,
      rlc_twoChannelPIMSEdgeProjection_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply] at happ
    have hdouble := congrArg (fun b : Bool => !b) happ
    simpa using hdouble
  · let discarded : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' :=
      ⟨e, hvisible⟩
    exact congrFun hdiscarded discarded


theorem rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (rho sigma : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :
    rlc_twoChannelPIMSEdgeProjection gamma gamma' rho e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma e.1 := by
  rw [rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply]
  unfold rlc_connectorCentralFaceAmbientConfig
  rw [dif_neg e.2, dif_neg e.2]


theorem rlc_twoChannelFullPIMSConfig_variable_eq_projection {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelFullPIMSConfig gamma gamma' omega e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
  rw [rlc_twoChannelFullPIMSConfig,
    rlc_twoChannelPIMSEdgePerm_variable,
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSConfig_variableTarget_apply]

end
end StatMech.Universality
