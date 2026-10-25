/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_centralFaceGraph_edge_site_mem {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈
      rlc_connectorCentralFaceEdges gamma gamma' := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      simpa [heq, Sym2.map_mk] using he.2

theorem rlc_centralFaceEdgeLift_graphEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorCentralFaceEdgeLift (e.1.map Subtype.val)
        (rlc_centralFaceGraph_edge_site_mem e) = e.1 := by
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_connectorCentralFaceEdgeLift_map]


theorem rlc_twoChannel_centralBits_eq_of_PIMS_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma')
    {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpims : rlc_connectorCentralFacePIMSConfig gamma gamma' rho =
      rlc_connectorCentralFacePIMSConfig gamma gamma' sigma)
    (source : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    rho source.1 = sigma source.1 := by
  obtain ⟨target, htarget⟩ := hcover source
  have happ := congrFun hpims target.1
  have hsourceMem := rlc_centralFaceGraph_edge_site_mem source
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply, htarget,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma' rho hsourceMem,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma' sigma hsourceMem,
    rlc_centralFaceEdgeLift_graphEdge] at happ
  have hdouble := congrArg (fun b : Bool => !b) happ
  simpa using hdouble


theorem rlc_twoChannel_PIMS_and_discardedBits_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma') :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_connectorCentralFacePIMSConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega),
        fun e : RlcTwoChannelDiscardedEdge gamma gamma' => omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  funext e
  by_cases hcentral : e.1 ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet
  · let source :
        (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
      ⟨e.1, hcentral⟩
    have hsource := rlc_twoChannel_centralBits_eq_of_PIMS_eq hcover hpims source
    simpa [source, rlc_twoChannelEdgeConfigExtend,
      rlc_twoChannelConfigSplitEquiv, e.2] using hsource
  · let discarded : RlcTwoChannelDiscardedEdge gamma gamma' :=
      ⟨e, hcentral⟩
    exact congrFun hdiscarded discarded


end
end StatMech.Universality
