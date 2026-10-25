/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelIndexedOuterConfig_le_closedSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega ≤
      rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false) := by
  intro a
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
          have hnotTrace : s(x, y) ∉
              (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
            intro hmem
            exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) = rho source := by
            change (if s(x, y) ∈
                (rlc_connectorTraceWiring gamma gamma').edgeFinset then
              true else rlc_twoChannelEdgeConfigExtend gamma gamma' rho
                s(x, y)) = rho source
            calc
              _ = rlc_twoChannelEdgeConfigExtend gamma gamma' rho
                    s(x, y) := if_neg hnotTrace
              _ = rho source := by
                change (if h : s(x, y) ∈
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
                  rho ⟨s(x, y), h⟩ else false) = rho source
                have hs : s(x, y) ∈
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
                  (SimpleGraph.mem_edgeSet _).mpr htwo
                rw [dif_pos hs]
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
                s(x, y))) = (!(omega source)) :=
              congrArg Bool.not (hforce omega)
            _ ≤ (!false) := Bool.le_true _
            _ ≤ (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
                s(x, y))) := (congrArg Bool.not
              (hforce (fun _ => false)).symm).le
        · have htraceMem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) =
                true := by
            unfold rlc_connectorForceTraceConfig
            exact if_pos htraceMem
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
                s(x, y))) = (!true) := congrArg Bool.not (hforce omega)
            _ ≤ (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
                s(x, y))) := (congrArg Bool.not
              (hforce (fun _ => false)).symm).le
  · exact le_rfl

theorem rlc_twoChannelFullIndexedOuterState_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullIndexedOuterState gamma gamma' omega ≤
      rlc_twoChannelFullIndexedOuterMaxState gamma gamma' := by
  intro a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterMaxState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterMaxState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact rlc_twoChannelIndexedOuterConfig_le_closedSource
      gamma gamma' omega a


theorem rlc_twoChannelFullIndexedOuterState_reconstruct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_psiExt (rlc_twoChannelFullInnerOuterVertex gamma gamma')
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega)
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelIndexedOuterConfig gamma gamma' omega := by
  apply FK.ocd_psiExt_innerRestrict_of_agreesOff
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')
  intro a ha
  rw [FK.ocd_mem_innerEdgeFinset] at ha
  exact (FK.ocd_outProj_eq_of_not_range
    (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) ha).symm

end
end StatMech.Universality
