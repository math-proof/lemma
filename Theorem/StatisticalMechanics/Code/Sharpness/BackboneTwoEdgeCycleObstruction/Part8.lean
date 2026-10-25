/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part8
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


theorem residualCycle₀_ne_suffix : residualCycle₀ ≠ residualSuffix := by
  intro h
  apply cycleEdge₀_ne_suffixEdge
  apply Subtype.ext
  simpa [residualCycle₀, residualSuffix, residualEdge] using
    congrArg Subtype.val h


theorem residual_complete_suffixEven :
    BackboneTwoEdgeBondProgram.program.CompleteEvent
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge))
      [canonicalEdgeSegment domain.graph suffixEdge]
      (restrictResidual suffixEvenFlux) := by
  let d' := shb_BackboneExplorationDomain.advance domain
    (canonicalEdgeSegment domain.graph headEdge)
  have hunit := program_complete_canonical_singleton_unitFlux d'
    residualSuffix
    (residualEdge_active_advance domain headEdge suffixEdge
      headEdge_ne_suffixEdge suffix_active)
  have hunit' :
      BackboneTwoEdgeBondProgram.program.CompleteEvent d'
        [canonicalEdgeSegment domain.graph suffixEdge]
        (unitFlux d'.graph residualSuffix) := by
    simpa only [d', residualGraph, residualSuffix,
      residualEdge_canonical_eq] using hunit
  have hodd : ∀ e : d'.graph.edgeFinset,
      oddBit (restrictResidual suffixEvenFlux e) =
        oddBit (unitFlux d'.graph residualSuffix e) := by
    intro e
    let ambient : domain.graph.edgeFinset :=
      ⟨e.1, edgeFinset_subset residualLe e.2⟩
    rcases edge_cases ambient with hhead | hsuffix | hc₀ | hc₁ | hc₂
    · have hmem := e.2
      change e.1 ∈ residualGraph.edgeFinset at hmem
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
        canonicalEdgeSegment_edgeSet] at hmem
      have heval : e.1 = headEdge.1 := by
        simpa [ambient] using congrArg Subtype.val hhead
      exact (hmem.2 (by simp [heval])).elim
    · have he : e = residualSuffix := by
        apply Subtype.ext
        simpa [ambient, residualSuffix, residualEdge] using
          congrArg Subtype.val hsuffix
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hsuffix, suffixEvenFlux_suffix, if_pos he]
    · have he : e = residualCycle₀ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₀, residualEdge] using
          congrArg Subtype.val hc₀
      have hne : e ≠ residualSuffix := fun h =>
        residualCycle₀_ne_suffix (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₀, suffixEvenFlux_cycle₀, if_neg hne]
      decide
    · have he : e = residualCycle₁ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₁, residualEdge] using
          congrArg Subtype.val hc₁
      have hresne : residualCycle₁ ≠ residualSuffix := by
        intro h
        apply cycleEdge₁_ne_suffixEdge
        apply Subtype.ext
        simpa [residualCycle₁, residualSuffix, residualEdge] using
          congrArg Subtype.val h
      have hne : e ≠ residualSuffix := fun h => hresne (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₁, suffixEvenFlux_cycle₁, if_neg hne]
      decide
    · have he : e = residualCycle₂ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₂, residualEdge] using
          congrArg Subtype.val hc₂
      have hresne : residualCycle₂ ≠ residualSuffix := by
        intro h
        apply cycleEdge₂_ne_suffixEdge
        apply Subtype.ext
        simpa [residualCycle₂, residualSuffix, residualEdge] using
          congrArg Subtype.val h
      have hne : e ≠ residualSuffix := fun h => hresne (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₂, suffixEvenFlux_cycle₂, if_neg hne]
      decide
  have hbits :
      fluxBitConfig d'.graph
          (BackboneTwoEdgeBondProgram.program (V := Fin 6)).bit
          (restrictResidual suffixEvenFlux) =
        fluxBitConfig d'.graph
          (BackboneTwoEdgeBondProgram.program (V := Fin 6)).bit
          (unitFlux d'.graph residualSuffix) := by
    change fluxBitConfig d'.graph oddBit (restrictResidual suffixEvenFlux) =
      fluxBitConfig d'.graph oddBit (unitFlux d'.graph residualSuffix)
    funext b
    unfold fluxBitConfig
    split
    · rename_i hleft
      split
      · rename_i hright
        convert hodd ⟨b, hleft⟩ using 1
      · rename_i hright
        exact (hright hleft).elim
    · rename_i hleft
      split
      · rename_i hright
        exact (hleft hright).elim
      · rfl
  change BackboneTwoEdgeBondProgram.program.CompleteEvent d'
    [canonicalEdgeSegment domain.graph suffixEdge]
    (restrictResidual suffixEvenFlux)
  unfold BondwiseSegmentProgram.CompleteEvent
    BondwiseSegmentProgram.TerminalEvent BondwiseSuffixEvent at hunit' ⊢
  constructor
  · have heq := congrArg
      (fun config => (BackboneTwoEdgeBondProgram.program (V := Fin 6)).scan.Selects
        (fun _ e => config e)
        ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).initial d')
        ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).encode d'
          [canonicalEdgeSegment domain.graph suffixEdge])) hbits
    exact Eq.mpr heq hunit'.1
  · let st := BackboneTwoEdgeBondProgram.program.scan.residual
        (BackboneTwoEdgeBondProgram.program.initial d')
        (BackboneTwoEdgeBondProgram.program.encode d'
          [canonicalEdgeSegment domain.graph suffixEdge])
    have heq := congrArg
      (fun omega => (BackboneTwoEdgeBondProgram.program (V := Fin 6)).terminal
        st omega) hbits
    exact Eq.mpr heq hunit'.2


theorem suffixEven_event :
    ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
      domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge]).Event
      domain.graph suffixEvenFlux := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event]
  exact ⟨restrictResidual suffixEvenFlux,
    extendFlux_restrictResidual suffixEvenFlux suffixEvenFlux_head,
    ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).runSpec_event
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge))
      [canonicalEdgeSegment domain.graph suffixEdge]
      (restrictResidual suffixEvenFlux)).mpr residual_complete_suffixEven⟩

theorem sources_unitFlux_eq_toFinset
    (e : domain.graph.edgeFinset) :
    sources domain.graph (ofEdgeFun domain.graph (unitFlux domain.graph e)) =
      e.1.toFinset := by
  rw [sources_unitFlux]
  change {e.1.out.1, e.1.out.2} = e.1.toFinset
  rw [← Sym2.toFinset_mk_eq]
  exact congrArg Sym2.toFinset e.1.out_eq


theorem oddCycle_sources_empty :
    sources domain.graph (ofEdgeFun domain.graph oddCycleFlux) = ∅ := by
  change sources domain.graph (ofEdgeFun domain.graph
    (fun e => (unitFlux domain.graph cycleEdge₀ e +
      unitFlux domain.graph cycleEdge₁ e) +
      unitFlux domain.graph cycleEdge₂ e)) = ∅
  rw [← ofEdgeFun_add, ← ofEdgeFun_add, sources_add, sources_add,
    sources_unitFlux_eq_toFinset, sources_unitFlux_eq_toFinset,
    sources_unitFlux_eq_toFinset]
  change s((3 : Fin 6), 4).toFinset ∆ s((4 : Fin 6), 5).toFinset ∆
    s((5 : Fin 6), 3).toFinset = ∅
  decide


theorem oddCycle_vacuum_event :
    (residualVacuumRunSpec domain
      (canonicalEdgeSegment domain.graph headEdge)).Event
      domain.graph oddCycleFlux := by
  rw [residualVacuumRunSpec_event]
  unfold liftedResidualVacuum
  refine ⟨restrictResidual oddCycleFlux,
    extendFlux_restrictResidual oddCycleFlux oddCycleFlux_head, ?_⟩
  change sources residualGraph
    (ofEdgeFun residualGraph (restrictResidual oddCycleFlux)) = ∅
  rw [← sources_extendFlux residualLe]
  rw [extendFlux_restrictResidual oddCycleFlux oddCycleFlux_head]
  exact oddCycle_sources_empty


theorem suffix_event_cycle₀_not_odd
    (p : domain.graph.edgeFinset → Nat)
    (h : ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
      domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph p) :
    ¬ Odd (p cycleEdge₀) := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
  obtain ⟨r, hrext, hrun⟩ := h
  rw [(BackboneTwoEdgeBondProgram.program (V := Fin 6)).runSpec_event] at hrun
  obtain ⟨e, heSegment, _, _, _, hfinished⟩ :=
    program_complete_singleton_data
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge)) r
      (canonicalEdgeSegment domain.graph suffixEdge) hrun
  have heResidual : e = residualSuffix := by
    apply canonicalEdgeSegment_injective residualGraph
    calc
      canonicalEdgeSegment residualGraph e =
          canonicalEdgeSegment domain.graph suffixEdge := heSegment
      _ = canonicalEdgeSegment residualGraph residualSuffix :=
        (residualEdge_canonical_eq domain headEdge suffixEdge
          headEdge_ne_suffixEdge).symm
  subst e
  intro hpOdd
  have hrOdd : Odd (r residualCycle₀) := by
    have hval := congrFun hrext cycleEdge₀
    have hmem : cycleEdge₀.1 ∈ residualGraph.edgeFinset :=
      secondEdge_mem_delete domain headEdge cycleEdge₀
        headEdge_ne_cycleEdge₀
    have hval' : r residualCycle₀ = p cycleEdge₀ := by
      unfold extendFlux at hval
      split at hval
      · rename_i hm
        convert hval using 1
      · rename_i hm
        exact (hm hmem).elim
    rwa [hval']
  have htrue : fluxBitConfig residualGraph oddBit r cycleEdge₀.1 = true := by
    unfold fluxBitConfig
    split
    · rename_i hm
      have : r ⟨cycleEdge₀.1, hm⟩ = r residualCycle₀ := by
        congr 1
      rw [this]
      exact (oddBit_eq_true_iff _).mpr hrOdd
    · rename_i hm
      exact (hm residualCycle₀.2).elim
  have hfind :
      (residualGraph.edgeFinset.erase residualSuffix.1).1.toList.find?
          (fun b => fluxBitConfig residualGraph oddBit r b) = none := by
    simpa [BackboneTwoEdgeBondProgram.scan,
      shb_DynamicEdgeExploration.firstAdmissible] using hfinished
  have hmemList : cycleEdge₀.1 ∈
      (residualGraph.edgeFinset.erase residualSuffix.1).1.toList := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_erase.mpr
    refine ⟨?_, residualCycle₀.2⟩
    intro hval
    apply residualCycle₀_ne_suffix
    exact Subtype.ext hval
  exact ((List.find?_eq_none.mp hfind) cycleEdge₀.1 hmemList htrue).elim


end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
