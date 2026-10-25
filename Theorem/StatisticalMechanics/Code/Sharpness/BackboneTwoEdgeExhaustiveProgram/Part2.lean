/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram.Part2
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

theorem noFurtherOdd_twoUnit
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) :
    NoFurtherOdd ⟨d, [e.1, f.1]⟩ e.1 f.1
      (fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)) := by
  intro g hg hge hgf
  have hsube : (⟨g, hg⟩ : d.graph.edgeFinset) ≠ e := by
    intro h
    exact hge (congrArg Subtype.val h)
  have hsubf : (⟨g, hg⟩ : d.graph.edgeFinset) ≠ f := by
    intro h
    exact hgf (congrArg Subtype.val h)
  simp [fluxBitConfig, hg, oddBit,
    BackboneTwoEdgeBondProgram.twoUnitFlux, unitFlux, hsube, hsubf]


theorem program_complete_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
  have hbase :=
    BackboneTwoEdgeBondProgram.program_complete_canonical_pair_twoUnitFlux
      d e f hne hfirst hactiveE hactiveF hpath
  have hbaseTerminal := hbase.2
  unfold BondwiseSegmentProgram.CompleteEvent at hbase ⊢
  constructor
  · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
  · unfold BondwiseSegmentProgram.TerminalEvent at hbaseTerminal ⊢
    have hstate :
        program.scan.residual (program.initial d)
            (program.encode d
              [canonicalEdgeSegment d.graph e,
                canonicalEdgeSegment d.graph f]) =
          (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
      simp [program, BackboneTwoEdgeBondProgram.encode,
        edgeOfSegment?_canonicalEdgeSegment,
        BackboneTwoEdgeBondProgram.scan]
    have hbaseState :
        BackboneTwoEdgeBondProgram.program.scan.residual
            (BackboneTwoEdgeBondProgram.program.initial d)
            (BackboneTwoEdgeBondProgram.program.encode d
              [canonicalEdgeSegment d.graph e,
                canonicalEdgeSegment d.graph f]) =
          (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
      simp [BackboneTwoEdgeBondProgram.program,
        BackboneTwoEdgeBondProgram.encode,
        edgeOfSegment?_canonicalEdgeSegment,
        BackboneTwoEdgeBondProgram.scan]
    rw [hstate]
    rw [hbaseState] at hbaseTerminal
    exact ⟨hbaseTerminal, noFurtherOdd_twoUnit d e f⟩


theorem selectorSpec_fiber_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    (selectorSpec (V := V)).toPartialSelector.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
    hactiveE hactiveF hpath


theorem noFurtherOdd_of_complete_canonical_pair
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (m : d.graph.edgeFinset -> Nat)
    (h : program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] m) :
    NoFurtherOdd
      (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) e.1 f.1
      (fluxBitConfig d.graph oddBit m) := by
  have hterminal := h.2
  unfold BondwiseSegmentProgram.TerminalEvent at hterminal
  have hstate :
      program.scan.residual (program.initial d)
          (program.encode d
            [canonicalEdgeSegment d.graph e,
              canonicalEdgeSegment d.graph f]) =
        (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
    simp [program, BackboneTwoEdgeBondProgram.encode,
      edgeOfSegment?_canonicalEdgeSegment,
      BackboneTwoEdgeBondProgram.scan]
  rw [hstate] at hterminal
  simpa [program, terminal] using hterminal.2


theorem runSpec_singleton_event_iff_base
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    ((program (V := V)).runSpec d [s]).Event d.graph m <->
      ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [s]).Event
        d.graph m := by
  rw [(program (V := V)).runSpec_event,
    (BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event]
  exact program_complete_singleton_iff_base d s m


theorem liftedResidualRunSpec_singleton_event_iff_base
    (d : shb_ExplorationDomain V) (s t : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    ((program (V := V)).liftedResidualRunSpec d s [t]).Event d.graph m <->
      ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec
        d s [t]).Event d.graph m := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event,
    BondwiseSegmentProgram.liftedResidualRunSpec_event]
  unfold BondwiseSegmentProgram.LiftedRunEvent LiftedPredicate
  constructor
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (runSpec_singleton_event_iff_base
      (shb_BackboneExplorationDomain.advance d s) t r).mp hrun⟩
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (runSpec_singleton_event_iff_base
      (shb_BackboneExplorationDomain.advance d s) t r).mpr hrun⟩


theorem fullRun_activeHead_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
      ((program (V := V)).runSpec d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
      d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
      {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
  rw [BackboneTwoEdgeBondToggle.bondwiseRunToggleCovariance_twoUnit_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_zero_false d e f hpath
        (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph f)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_second_unitFlux_false
        d e f hactiveE hpath ha).elim
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (unitFlux d.graph e)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_unitFlux_first_false
        d e f hpath (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_twoUnitFlux_false
        d e f hactiveE hpath ha).elim
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (unitFlux d.graph f)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_unitFlux_second_false
        d e f hpath (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_zero_false
        d e hactiveE ha).elim
  · constructor
    · intro _
      exact (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph e)).mpr
        (BackboneTwoEdgeBondToggle.activeSegmentFiber_unitFlux
          d e hactiveE)
    · intro _
      exact ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)).mpr
        (program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
          hactiveE hactiveF hpath)


theorem residualVacuum_suffix_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
    BondwiseRunToggleCovariance
      (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
      ((program (V := V)).liftedResidualRunSpec d
        (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
      d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
      {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
  intro T
  have hbase :=
    BackboneTwoEdgeBondToggle.residualVacuum_suffix_twoUnit_covariance
      d e f hne hactiveF T
  constructor
  · intro hvacuum
    apply (liftedResidualRunSpec_singleton_event_iff_base d
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)
      (profileFlux d.graph
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}))).mpr
    exact hbase.mp hvacuum
  · intro hsuffix
    apply hbase.mpr
    exact (liftedResidualRunSpec_singleton_event_iff_base d
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)
      (profileFlux d.graph
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}))).mp
      hsuffix


theorem twoUnit_componentwise_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
        ((program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} /\
      BondwiseRunToggleCovariance
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        ((program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} :=
  ⟨fullRun_activeHead_twoUnit_covariance d e f hne hfirst hactiveE
      hactiveF hpath,
    residualVacuum_suffix_twoUnit_covariance d e f hne hactiveF⟩


theorem twoUnit_pair_toggle
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f))
    (T : Finset (Copy d.graph
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f))) :
    BondwisePairEvent
        ((program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) T <->
      BondwisePairEvent
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        ((program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}) := by
  obtain ⟨hfull, hresidual⟩ := twoUnit_componentwise_covariance d e f hne
    hfirst hactiveE hactiveF hpath
  exact BondwisePairEvent.toggle_iff_of_componentwise
    ((program (V := V)).runSpec d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
    (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
    ((program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
    {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}
    hfull hresidual T


end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
