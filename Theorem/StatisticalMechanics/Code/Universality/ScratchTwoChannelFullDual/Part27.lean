/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part32
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullVariableExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing
      (rlc_twoChannelFullVariableExteriorEvent gamma gamma') := by
  intro eta eta' heta
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [SimpleGraph.sup_adj, FK.openSub_adj] at huv ⊢
  rcases huv with ⟨hvar, hopen⟩ | hext
  · refine Or.inl ⟨hvar, ?_⟩
    have he : s(u, v) ∈
        (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hvar
    have hopen' : eta ⟨s(u, v), he⟩ = true := by
      simpa [FK.extendActive, he] using hopen
    have hopen'' : eta' ⟨s(u, v), he⟩ = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hfalse
      have hle := heta ⟨s(u, v), he⟩
      rw [hopen', hfalse] at hle
      exact (show ¬((true : Bool) ≤ false) by decide) hle
    simpa [FK.extendActive, he] using hopen''
  · exact Or.inr hext

theorem rlc_twoChannelFullInnerExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  intro rho sigma hrs hrho
  exact rlc_twoChannelFullVariableExteriorEvent_isIncreasing gamma gamma'
    (fun target => hrs _)
    hrho


theorem rlc_twoChannelFullIndexed_innerExteriorEvent_iff_fullDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) ∈
        rlc_twoChannelFullInnerExteriorEvent gamma gamma' ↔
      rlc_twoChannelFullDualConfig gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  unfold rlc_twoChannelFullInnerExteriorEvent
  change rlc_twoChannelFullInnerToVariable gamma gamma'
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) ∈
      rlc_twoChannelFullVariableExteriorEvent gamma gamma' ↔ _
  rw [rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection]
  exact (rlc_twoChannelFullDual_mem_event_iff_variableExterior
    gamma gamma' omega).symm


theorem rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega omega' : RlcTwoChannelEdgeConfig gamma gamma')
    (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma',
      omega e.1 = omega' e.1) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
      (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)
      (rlc_twoChannelIndexedOuterConfig gamma gamma' omega') := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.2
        rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
        change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
        rcases hfmem with htwo | htrace
        · let source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
            ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
          have hnotRange : source ∉ Set.range
              (rlc_twoChannelFullSourceEdge
                (gamma := gamma) (gamma' := gamma')) := by
            rintro ⟨target, htarget⟩
            apply haRange
            have hf : f = rlc_twoChannelIndexedAugmentedEdge target := by
              apply Subtype.ext
              change f.1 = (rlc_twoChannelFullSourceEdge target).1
              exact hedge.trans (congrArg Subtype.val htarget).symm
            rw [← hrandom.choose_spec]
            change rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
              Set.range (FK.ocd_innerEdge
                (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            rw [hf]
            exact rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange
              target
          have hnotTrace : s(x, y) ∉
              (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
            intro hmem
            exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho) f.1 =
                rho source := by
            unfold rlc_connectorForceTraceConfig
            rw [if_neg (hedge ▸ hnotTrace)]
            rw [hedge]
            change (if h : s(x, y) ∈
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
              rho ⟨s(x, y), h⟩ else false) = rho source
            have hs : s(x, y) ∈
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
              (SimpleGraph.mem_edgeSet _).mpr htwo
            rw [dif_pos hs]
          have hforce' (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) = rho source := by
            simpa [hedge] using hforce rho
          apply congrArg Bool.not
          exact (hforce' omega').trans <|
            (hdiscarded ⟨source, hnotRange⟩).symm.trans
              (hforce' omega).symm
        · have htraceMem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                s(x, y) = true := by
            unfold rlc_connectorForceTraceConfig
            exact if_pos htraceMem
          apply congrArg Bool.not
          exact (hforce omega').trans (hforce omega).symm
  · rfl


end
end StatMech.Universality
