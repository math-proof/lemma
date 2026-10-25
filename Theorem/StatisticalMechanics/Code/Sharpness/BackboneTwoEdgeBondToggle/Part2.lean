/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part2
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondToggle

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneTwoEdgeBondProgram

open BackboneDeterminedCutSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

theorem residualEdge_canonical_eq
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    canonicalEdgeSegment
        (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
        (residualEdge d e f hne) = canonicalEdgeSegment d.graph f := by
  simp [canonicalEdgeSegment, residualEdge]


theorem distinct_canonical_compatible
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    shb_BackboneExplorationDomain.compatible
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) := by
  rw [shb_BackboneExplorationDomain.compatible,
    canonicalEdgeSegment_edgeSet, canonicalEdgeSegment_edgeSet]
  exact Set.disjoint_singleton.mpr (fun hef => hne (Subtype.ext hef))


theorem residualEdge_active_advance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (hactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    canonicalEdgeSegment
        (shb_BackboneExplorationDomain.advance d
          (canonicalEdgeSegment d.graph e)).graph
        (residualEdge d e f hne) ∈
      (shb_BackboneExplorationDomain.advance d
        (canonicalEdgeSegment d.graph e)).active := by
  change canonicalEdgeSegment
      (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
      (residualEdge d e f hne) ∈
    d.active.filter
      (shb_BackboneExplorationDomain.compatible
        (canonicalEdgeSegment d.graph e))
  rw [residualEdge_canonical_eq]
  simp [hactive, distinct_canonical_compatible d e f hne]


theorem extendFlux_residual_unitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    extendFlux (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet)
        (unitFlux
          (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
          (residualEdge d e f hne)) = unitFlux d.graph f := by
  funext g
  unfold extendFlux unitFlux
  split
  · rename_i hg
    by_cases hgf : g = f
    · subst g
      have hsubeq :
          (⟨f.1, hg⟩ :
              (d.graph.deleteEdges
                (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset) =
            residualEdge d e f hne := Subtype.ext rfl
      simp [hsubeq]
    · have hsub :
          (⟨g.1, hg⟩ :
              (d.graph.deleteEdges
                (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset) ≠
            residualEdge d e f hne := by
        intro h
        have hv : g.1 = f.1 := congrArg
          (fun x : (d.graph.deleteEdges
            (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset => x.1) h
        exact hgf (Subtype.ext hv)
      simp [hgf, hsub]
  · rename_i hg
    by_cases hgf : g = f
    · subst g
      exact (hg (secondEdge_mem_delete d e f hne)).elim
    · simp [hgf]


theorem firstEndpoints_ne_secondEndpoints
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    ({(canonicalEdgeSegment G e).1,
        (canonicalEdgeSegment G e).2.1} : Finset V) ≠
      ({(canonicalEdgeSegment G f).1,
        (canonicalEdgeSegment G f).2.1} : Finset V) := by
  let s := canonicalEdgeSegment G e
  let t := canonicalEdgeSegment G f
  change ({s.1, s.2.1} : Finset V) ≠ {t.1, t.2.1}
  have hsne : s.1 ≠ s.2.1 := canonicalEdgeSegment_start_ne_end G e
  have hastart : s.1 ≠ t.1 := by
    intro h
    exact hsne (h.trans hpath.1.symm)
  intro heq
  have ha : s.1 ∈ ({t.1, t.2.1} : Finset V) := by
    rw [← heq]
    simp
  rw [Finset.mem_insert, Finset.mem_singleton] at ha
  exact ha.elim hastart hpath.2

theorem firstEndpoints_ne_pairBoundary
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    ({(canonicalEdgeSegment G e).1,
        (canonicalEdgeSegment G e).2.1} : Finset V) ≠
      ({(canonicalEdgeSegment G e).1,
          (canonicalEdgeSegment G e).2.1} ∆
        {(canonicalEdgeSegment G f).1,
          (canonicalEdgeSegment G f).2.1} : Finset V) := by
  let s := canonicalEdgeSegment G e
  let t := canonicalEdgeSegment G f
  change ({s.1, s.2.1} : Finset V) ≠
    {s.1, s.2.1} ∆ {t.1, t.2.1}
  have htne : t.1 ≠ t.2.1 := canonicalEdgeSegment_start_ne_end G f
  have hca : t.2.1 ≠ s.1 := hpath.2.symm
  have hcb : t.2.1 ≠ s.2.1 := by
    intro h
    exact htne (hpath.1.symm.trans h.symm)
  have hnotFirst : t.2.1 ∉ ({s.1, s.2.1} : Finset V) := by
    simp [hca, hcb]
  have hmem : t.2.1 ∈
      ({s.1, s.2.1} : Finset V) ∆ {t.1, t.2.1} := by
    rw [Finset.mem_symmDiff]
    exact Or.inr ⟨by simp, hnotFirst⟩
  intro heq
  rw [← heq] at hmem
  exact hnotFirst hmem

theorem secondEndpoints_ne_pairBoundary
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    ({(canonicalEdgeSegment G f).1,
        (canonicalEdgeSegment G f).2.1} : Finset V) ≠
      ({(canonicalEdgeSegment G e).1,
          (canonicalEdgeSegment G e).2.1} ∆
        {(canonicalEdgeSegment G f).1,
          (canonicalEdgeSegment G f).2.1} : Finset V) := by
  let s := canonicalEdgeSegment G e
  let t := canonicalEdgeSegment G f
  change ({t.1, t.2.1} : Finset V) ≠
    {s.1, s.2.1} ∆ {t.1, t.2.1}
  have hsne : s.1 ≠ s.2.1 := canonicalEdgeSegment_start_ne_end G e
  have hastart : s.1 ≠ t.1 := by
    intro h
    exact hsne (h.trans hpath.1.symm)
  have haend : s.1 ≠ t.2.1 := hpath.2
  have hnotSecond : s.1 ∉ ({t.1, t.2.1} : Finset V) := by
    simp [hastart, haend]
  have hmem : s.1 ∈
      ({s.1, s.2.1} : Finset V) ∆ {t.1, t.2.1} := by
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨by simp, hnotSecond⟩
  intro heq
  rw [← heq] at hmem
  exact hnotSecond hmem


@[simp] theorem sources_ofEdgeFun_zero (G : SimpleGraph V) :
    sources G (ofEdgeFun G (0 : G.edgeFinset -> Nat)) = ∅ := by
  ext x
  simp [mem_sources, incidentFlux, ofEdgeFun]

theorem program_pair_zero_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] 0 := by
  intro h
  have hsource := sources_eq_sourceClass_of_program_complete d 0 _ h
  change sources d.graph (ofEdgeFun d.graph 0) =
    {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1} ∆
      {(canonicalEdgeSegment d.graph f).1,
        (canonicalEdgeSegment d.graph f).2.1} at hsource
  apply canonicalPair_boundary_ne_empty d.graph e f hpath
  calc
    _ = sources d.graph (ofEdgeFun d.graph 0) := hsource.symm
    _ = ∅ := sources_ofEdgeFun_zero d.graph

theorem program_pair_unitFlux_first_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (unitFlux d.graph e) := by
  intro h
  have hsource := sources_eq_sourceClass_of_program_complete d
    (unitFlux d.graph e) _ h
  change sources d.graph (ofEdgeFun d.graph (unitFlux d.graph e)) =
    {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1} ∆
      {(canonicalEdgeSegment d.graph f).1,
        (canonicalEdgeSegment d.graph f).2.1} at hsource
  rw [sources_unitFlux] at hsource
  exact firstEndpoints_ne_pairBoundary d.graph e f hpath hsource

theorem program_pair_unitFlux_second_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (unitFlux d.graph f) := by
  intro h
  have hsource := sources_eq_sourceClass_of_program_complete d
    (unitFlux d.graph f) _ h
  change sources d.graph (ofEdgeFun d.graph (unitFlux d.graph f)) =
    {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1} ∆
      {(canonicalEdgeSegment d.graph f).1,
        (canonicalEdgeSegment d.graph f).2.1} at hsource
  rw [sources_unitFlux] at hsource
  exact secondEndpoints_ne_pairBoundary d.graph e f hpath hsource

theorem activeSegmentFiber_zero_false
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active) :
    ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs 0 := by
  rintro ⟨hsource, _⟩
  have hsource' : (∅ : Finset V) =
      {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1} := by
    simpa only [sources_ofEdgeFun_zero] using hsource
  have hmem : (canonicalEdgeSegment d.graph e).1 ∈ (∅ : Finset V) := by
    rw [hsource']
    simp
  simpa using hmem

theorem activeSegmentFiber_second_unitFlux_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs
      (unitFlux d.graph f) := by
  rintro ⟨hsource, _⟩
  rw [sources_unitFlux] at hsource
  exact firstEndpoints_ne_secondEndpoints d.graph e f hpath hsource.symm

theorem activeSegmentFiber_twoUnitFlux_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs
      (twoUnitFlux d.graph e f) := by
  rintro ⟨hsource, _⟩
  rw [sources_twoUnitFlux] at hsource
  exact firstEndpoints_ne_pairBoundary d.graph e f hpath hsource.symm


theorem profileFlux_singleton_apply
    (G : SimpleGraph V) (m : G.edgeFinset -> Nat)
    (i : Copy G m) (g : G.edgeFinset) :
    profileFlux G m {i} g = if i.1 = g then 1 else 0 := by
  unfold profileFlux
  rw [Finset.filter_singleton]
  by_cases hig : i.1 = g <;> simp [hig]

theorem profileFlux_pair_apply
    (G : SimpleGraph V) (m : G.edgeFinset -> Nat)
    (i j : Copy G m) (hij : i ≠ j) (g : G.edgeFinset) :
    profileFlux G m {i, j} g =
      (if i.1 = g then 1 else 0) + (if j.1 = g then 1 else 0) := by
  unfold profileFlux
  rw [Finset.filter_insert, Finset.filter_singleton]
  by_cases hig : i.1 = g <;> by_cases hjg : j.1 = g <;>
    simp [hig, hjg, hij]

@[simp] theorem profileFlux_empty_twoUnitFlux
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    profileFlux G (twoUnitFlux G e f)
        (∅ : Finset (Copy G (twoUnitFlux G e f))) = 0 := by
  funext g
  simp [profileFlux]

@[simp] theorem profileFlux_firstCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    profileFlux G (twoUnitFlux G e f) {firstCopy G e f hne} =
      unitFlux G e := by
  funext g
  rw [profileFlux_singleton_apply]
  simp [firstCopy, unitFlux, eq_comm]

@[simp] theorem profileFlux_secondCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    profileFlux G (twoUnitFlux G e f) {secondCopy G e f hne} =
      unitFlux G f := by
  funext g
  rw [profileFlux_singleton_apply]
  simp [secondCopy, unitFlux, eq_comm]

@[simp] theorem profileFlux_bothCopies
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    profileFlux G (twoUnitFlux G e f)
        {firstCopy G e f hne, secondCopy G e f hne} =
      twoUnitFlux G e f := by
  funext g
  rw [profileFlux_pair_apply _ _ _ _
    (firstCopy_ne_secondCopy G e f hne)]
  simp [firstCopy, secondCopy, twoUnitFlux, unitFlux, eq_comm]
  rfl

@[simp] theorem empty_symmDiff_secondCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    (∅ : Finset (Copy G (twoUnitFlux G e f))) ∆
        ({secondCopy G e f hne} :
          Finset (Copy G (twoUnitFlux G e f))) =
      ({secondCopy G e f hne} :
        Finset (Copy G (twoUnitFlux G e f))) := by
  ext i
  have hfe : secondCopy G e f hne ≠ firstCopy G e f hne :=
    (firstCopy_ne_secondCopy G e f hne).symm
  rcases copy_eq_first_or_second G e f hne i with rfl | rfl <;>
    simp [Finset.mem_symmDiff, firstCopy_ne_secondCopy G e f hne, hfe]

@[simp] theorem firstCopy_symmDiff_secondCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    ({firstCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) ∆
        {secondCopy G e f hne} =
      ({firstCopy G e f hne, secondCopy G e f hne} :
        Finset (Copy G (twoUnitFlux G e f))) := by
  ext i
  have hfe : secondCopy G e f hne ≠ firstCopy G e f hne :=
    (firstCopy_ne_secondCopy G e f hne).symm
  rcases copy_eq_first_or_second G e f hne i with rfl | rfl <;>
    simp [Finset.mem_symmDiff, firstCopy_ne_secondCopy G e f hne, hfe]

@[simp] theorem secondCopy_symmDiff_self
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    ({secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) ∆
        {secondCopy G e f hne} =
      (∅ : Finset (Copy G (twoUnitFlux G e f))) := by
  ext i
  have hfe : secondCopy G e f hne ≠ firstCopy G e f hne :=
    (firstCopy_ne_secondCopy G e f hne).symm
  rcases copy_eq_first_or_second G e f hne i with rfl | rfl <;>
    simp [Finset.mem_symmDiff, firstCopy_ne_secondCopy G e f hne, hfe]

@[simp] theorem bothCopies_symmDiff_secondCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    ({firstCopy G e f hne, secondCopy G e f hne} :
        Finset (Copy G (twoUnitFlux G e f))) ∆
        {secondCopy G e f hne} =
      ({firstCopy G e f hne} :
        Finset (Copy G (twoUnitFlux G e f))) := by
  ext i
  have hfe : secondCopy G e f hne ≠ firstCopy G e f hne :=
    (firstCopy_ne_secondCopy G e f hne).symm
  rcases copy_eq_first_or_second G e f hne i with rfl | rfl <;>
    simp [Finset.mem_symmDiff, firstCopy_ne_secondCopy G e f hne, hfe]


theorem bondwiseRunToggleCovariance_twoUnit_iff
    (E F : BondwiseRunSpec V)
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    BondwiseRunToggleCovariance E F G (twoUnitFlux G e f)
        {secondCopy G e f hne} <->
      (E.Event G 0 <-> F.Event G (unitFlux G f)) /\
      (E.Event G (unitFlux G e) <-> F.Event G (twoUnitFlux G e f)) /\
      (E.Event G (unitFlux G f) <-> F.Event G 0) /\
      (E.Event G (twoUnitFlux G e f) <-> F.Event G (unitFlux G e)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h (∅ : Finset (Copy G (twoUnitFlux G e f)))
    · simpa using h
        ({firstCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f)))
    · simpa using h
        ({secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f)))
    · simpa using h
        ({firstCopy G e f hne, secondCopy G e f hne} :
          Finset (Copy G (twoUnitFlux G e f)))
  · rintro ⟨hzero, hfirst, hsecond, hboth⟩ T
    rcases subset_eq_of_twoUnitFlux G e f hne T with
      rfl | rfl | rfl | rfl
    · simpa using hzero
    · simpa using hfirst
    · simpa using hsecond
    · simpa using hboth


theorem fullRun_activeHead_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
      ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
      d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} := by
  rw [bondwiseRunToggleCovariance_twoUnit_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have hc :=
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
          (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (program_pair_zero_false d e f hpath hc).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph f)).mp h
      exact (activeSegmentFiber_second_unitFlux_false d e f hactiveE
        hpath ha).elim
  · constructor
    · intro h
      have hc :=
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
          (unitFlux d.graph e)).mp h
      exact (program_pair_unitFlux_first_false d e f hpath hc).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (twoUnitFlux d.graph e f)).mp h
      exact (activeSegmentFiber_twoUnitFlux_false d e f hactiveE
        hpath ha).elim
  · constructor
    · intro h
      have hc :=
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
          (unitFlux d.graph f)).mp h
      exact (program_pair_unitFlux_second_false d e f hpath hc).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (activeSegmentFiber_zero_false d e hactiveE ha).elim
  · constructor
    · intro _
      exact (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph e)).mpr
        (activeSegmentFiber_unitFlux d e hactiveE)
    · intro _
      exact ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event
        d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (twoUnitFlux d.graph e f)).mpr
          (program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
            hactiveE hactiveF hpath)


theorem firstEdge_not_mem_delete
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    e.1 ∉ (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
    canonicalEdgeSegment_edgeSet]
  simp

theorem extendFlux_zero
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    extendFlux (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet)
        (0 : (d.graph.deleteEdges
          (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) = 0 := by
  funext g
  simp [extendFlux]

theorem liftedPredicate_zero_iff
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (P : ((d.graph.deleteEdges
      (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
    LiftedPredicate
        (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P 0 <->
      P 0 := by
  let hHG := d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet
  constructor
  · rintro ⟨r, hr, hPr⟩
    have hr0 : r = 0 := extendFlux_injective hHG
      (hr.trans (extendFlux_zero d e).symm)
    simpa [hr0] using hPr
  · intro hP
    exact ⟨0, extendFlux_zero d e, hP⟩

theorem liftedPredicate_second_iff
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (P : ((d.graph.deleteEdges
      (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
    LiftedPredicate
        (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P
        (unitFlux d.graph f) <->
      P (unitFlux
        (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
        (residualEdge d e f hne)) := by
  let hHG := d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet
  let rF := unitFlux
    (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
    (residualEdge d e f hne)
  constructor
  · rintro ⟨r, hr, hPr⟩
    have hrF : r = rF := extendFlux_injective hHG
      (hr.trans (extendFlux_residual_unitFlux d e f hne).symm)
    simpa [hrF] using hPr
  · intro hP
    exact ⟨rF, extendFlux_residual_unitFlux d e f hne, hP⟩

theorem not_lifted_first
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (P : ((d.graph.deleteEdges
      (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
    ¬LiftedPredicate
      (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P
      (unitFlux d.graph e) := by
  rintro ⟨r, hr, _⟩
  have heq := congrFun hr e
  simp [extendFlux, firstEdge_not_mem_delete d e, unitFlux] at heq

theorem not_lifted_twoUnit
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (P : ((d.graph.deleteEdges
      (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
    ¬LiftedPredicate
      (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P
      (twoUnitFlux d.graph e f) := by
  rintro ⟨r, hr, _⟩
  have heq := congrFun hr e
  simp [extendFlux, firstEdge_not_mem_delete d e, twoUnitFlux,
    unitFlux, hne] at heq

theorem vacuum_zero
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)).Event d.graph 0 := by
  rw [residualVacuumRunSpec_event]
  unfold liftedResidualVacuum
  rw [liftedPredicate_zero_iff]
  exact sources_ofEdgeFun_zero _

theorem vacuum_second_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    ¬(residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)).Event d.graph
      (unitFlux d.graph f) := by
  rw [residualVacuumRunSpec_event]
  unfold liftedResidualVacuum
  rw [liftedPredicate_second_iff d e f hne]
  intro hsource
  change sources
      (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
      (ofEdgeFun
        (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
        (unitFlux
          (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
          (residualEdge d e f hne))) = ∅ at hsource
  rw [sources_unitFlux] at hsource
  have hmem :
      (canonicalEdgeSegment
        (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
        (residualEdge d e f hne)).1 ∈ (∅ : Finset V) := by
    rw [← hsource]
    simp
  simpa using hmem

theorem suffix_second
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
    ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]).Event
      d.graph (unitFlux d.graph f) := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event]
  change LiftedPredicate
    (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet)
    (fun r => ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec
      (shb_BackboneExplorationDomain.advance d
        (canonicalEdgeSegment d.graph e))
      [canonicalEdgeSegment d.graph f]).Event
      (shb_BackboneExplorationDomain.advance d
        (canonicalEdgeSegment d.graph e)).graph r)
    (unitFlux d.graph f)
  rw [liftedPredicate_second_iff d e f hne]
  rw [← residualEdge_canonical_eq d e f hne]
  have hrun := ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event
    (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e))
    [canonicalEdgeSegment
      (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
      (residualEdge d e f hne)]
    (unitFlux
      (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet)
      (residualEdge d e f hne))).mpr
    (program_complete_canonical_singleton_unitFlux
    (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e))
    (residualEdge d e f hne) (residualEdge_active_advance d e f hne hactiveF))
  convert hrun using 1

theorem suffix_zero_false
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) :
    ¬((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]).Event
      d.graph 0 := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event]
  change ¬LiftedPredicate
    (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet)
    (fun r => ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec
      (shb_BackboneExplorationDomain.advance d
        (canonicalEdgeSegment d.graph e))
      [canonicalEdgeSegment d.graph f]).Event
      (shb_BackboneExplorationDomain.advance d
        (canonicalEdgeSegment d.graph e)).graph r) 0
  rw [liftedPredicate_zero_iff]
  intro hrun
  let d' := shb_BackboneExplorationDomain.advance d
    (canonicalEdgeSegment d.graph e)
  have hrun' :
      ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d'
        [canonicalEdgeSegment d.graph f]).Event d'.graph 0 := by
    convert hrun using 1
  have hcomplete :=
    ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event d'
      [canonicalEdgeSegment d.graph f] 0).mp hrun'
  have hnil : BackboneTwoEdgeBondProgram.program.CompleteEvent d' [] 0 :=
    (BackboneTwoEdgeBondProgram.program_complete_nil_iff d' 0).mpr
      (sources_ofEdgeFun_zero _)
  exact complete_nil_singleton_false d' 0 (canonicalEdgeSegment d.graph f)
    hnil hcomplete


theorem residualVacuum_suffix_twoUnit_truthTable
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
    let vacuum := residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)
    let suffix :=
      (BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
        (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]
    (vacuum.Event d.graph 0 /\
      suffix.Event d.graph (unitFlux d.graph f)) /\
    (¬vacuum.Event d.graph (unitFlux d.graph e) /\
      ¬suffix.Event d.graph (twoUnitFlux d.graph e f)) /\
    (¬vacuum.Event d.graph (unitFlux d.graph f) /\
      ¬suffix.Event d.graph 0) /\
    (¬vacuum.Event d.graph (twoUnitFlux d.graph e f) /\
      ¬suffix.Event d.graph (unitFlux d.graph e)) := by
  dsimp only
  refine ⟨⟨vacuum_zero d e, suffix_second d e f hne hactiveF⟩, ?_, ?_, ?_⟩
  · constructor
    · intro h
      rw [residualVacuumRunSpec_event] at h
      exact not_lifted_first d e _ h
    · intro h
      rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
      exact not_lifted_twoUnit d e f hne _ h
  · exact ⟨vacuum_second_false d e f hne, suffix_zero_false d e f⟩
  · constructor
    · intro h
      rw [residualVacuumRunSpec_event] at h
      exact not_lifted_twoUnit d e f hne _ h
    · intro h
      rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
      exact not_lifted_first d e _ h

theorem residualVacuum_suffix_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
    BondwiseRunToggleCovariance
      (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
      ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
        (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
      d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} := by
  rw [bondwiseRunToggleCovariance_twoUnit_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ => suffix_second d e f hne hactiveF,
      fun _ => vacuum_zero d e⟩
  · constructor
    · intro h
      rw [residualVacuumRunSpec_event] at h
      exact (not_lifted_first d e _ h).elim
    · intro h
      rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
      exact (not_lifted_twoUnit d e f hne _ h).elim
  · exact ⟨fun h => (vacuum_second_false d e f hne h).elim,
      fun h => (suffix_zero_false d e f h).elim⟩
  · constructor
    · intro h
      rw [residualVacuumRunSpec_event] at h
      exact (not_lifted_twoUnit d e f hne _ h).elim
    · intro h
      rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
      exact (not_lifted_first d e _ h).elim


theorem twoUnit_componentwise_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} /\
      BondwiseRunToggleCovariance
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} :=
  ⟨fullRun_activeHead_twoUnit_covariance d e f hne hfirst hactiveE
      hactiveF hpath,
    residualVacuum_suffix_twoUnit_covariance d e f hne hactiveF⟩


theorem twoUnit_pair_toggle
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f))
    (T : Finset (Copy d.graph (twoUnitFlux d.graph e f))) :
    BondwisePairEvent
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        d.graph (twoUnitFlux d.graph e f) T <->
      BondwisePairEvent
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (twoUnitFlux d.graph e f)
          (T ∆ {secondCopy d.graph e f hne}) := by
  obtain ⟨hhead, hresidual⟩ := twoUnit_componentwise_covariance d e f hne
    hfirst hactiveE hactiveF hpath
  exact BondwisePairEvent.toggle_iff_of_componentwise
    ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
    (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
    ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne}
    hhead hresidual T


end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
