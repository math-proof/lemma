/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullDualConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e =
      !(rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_twoChannelFullDualConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims _ _


theorem rlc_twoChannelFullDualConfig_of_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n))
    (f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (hf : f.1.map Subtype.val =
      rlc_pimsEdgeEquiv (e.map Subtype.val)) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e = !(omega f) := by
  rw [rlc_twoChannelFullDualConfig_apply]
  have hsource : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      (rlc_pimsEdgeEquiv (e.map Subtype.val)) = omega f := by
    rw [← hf, rlc_twoChannelFullAmbientConfig_source]
  rw [hsource]


theorem rlc_twoChannelFullDualConfig_of_no_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n))
    (hsource : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (e.map Subtype.val)))) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e =
      if rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then
        false
      else true := by
  rw [rlc_twoChannelFullDualConfig_apply]
  unfold rlc_twoChannelFullAmbientConfig
  rw [dif_neg hsource]
  split <;> rfl


theorem rlc_twoChannelFullDualConfig_variable_eq_projection {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelFullDualConfig gamma gamma' omega e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
  rw [rlc_twoChannelFullDualConfig_of_source gamma gamma' omega e.1
      (rlc_twoChannelPIMSSourceEdge e)
      (rlc_twoChannelPIMSSourceEdge_map e),
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSConfig_variableTarget_apply]


theorem rlc_twoChannelFullAmbientConfig_embeddedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (Ising.kwg_embeddedEdge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f) =
      rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 := by
  classical
  induction hf : f.1 using Sym2.inductionOn with
  | _ x y =>
      change RlcConnectorVertex n at x y
      have hcarrier :
          (rlc_connectorTwoChannelGraph gamma gamma' ⊔
            rlc_connectorTraceWiring gamma gamma').Adj x y := by
        have hfmem := f.2
        rw [hf, SimpleGraph.mem_edgeSet] at hfmem
        exact hfmem
      rcases hcarrier with htwo | htrace
      · have hedge : s(x, y) ∈
            (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact htwo
        have hnotTrace : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        rw [Ising.kwg_embeddedEdge]
        simp only [rlc_connectorTwoChannelAugmentedPlanarDomain,
          hf, Sym2.map_mk]
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y)
        have hsource := rlc_twoChannelFullAmbientConfig_source
          gamma gamma' omega ⟨s(x, y), hedge⟩
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          omega ⟨s(x, y), hedge⟩ at hsource
        rw [hsource]
        simp [rlc_connectorForceTraceConfig, hnotTrace,
          rlc_twoChannelEdgeConfigExtend,
          rlc_twoChannelConfigSplitEquiv, hedge]
      · have htraceMem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        rw [Ising.kwg_embeddedEdge]
        simp only [rlc_connectorTwoChannelAugmentedPlanarDomain,
          hf, Sym2.map_mk]
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y)
        rw [rlc_twoChannelFullAmbientConfig_trace gamma gamma' omega htrace.2]
        simp [rlc_connectorForceTraceConfig, htraceMem]


end
end StatMech.Universality
