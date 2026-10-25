/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle
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

@[simp] theorem firstCopy_edge
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    (firstCopy G e f hne).1 = e := rfl

@[simp] theorem secondCopy_edge
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    (secondCopy G e f hne).1 = f := rfl

theorem firstCopy_ne_secondCopy
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    firstCopy G e f hne ≠ secondCopy G e f hne := by
  intro h
  exact hne (congrArg Sigma.fst h)


theorem copy_eq_first_or_second
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f)
    (i : Copy G (twoUnitFlux G e f)) :
    i = firstCopy G e f hne ∨ i = secondCopy G e f hne := by
  rcases i with ⟨g, j⟩
  have hi : 0 < twoUnitFlux G e f g :=
    Fin.pos_iff_nonempty.mpr ⟨j⟩
  simp only [twoUnitFlux, unitFlux] at hi
  by_cases hie : g = e
  · left
    subst g
    unfold firstCopy
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Fin.ext
    change j.val = 0
    have hj := j.isLt
    simp [twoUnitFlux, unitFlux, hne] at hj
    omega
  · have hif : g = f := by
      by_contra hif
      simp [hie, hif] at hi
    right
    subst g
    unfold secondCopy
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Fin.ext
    change j.val = 0
    have hj := j.isLt
    simp [twoUnitFlux, unitFlux, hie] at hj
    omega


theorem copy_univ_eq_pair
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f) :
    (univ : Finset (Copy G (twoUnitFlux G e f))) =
      {firstCopy G e f hne, secondCopy G e f hne} := by
  ext i
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  exact copy_eq_first_or_second G e f hne i


theorem subset_eq_of_twoUnitFlux
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e ≠ f)
    (T : Finset (Copy G (twoUnitFlux G e f))) :
    T = ∅ ∨
      T = {firstCopy G e f hne} ∨
      T = {secondCopy G e f hne} ∨
      T = {firstCopy G e f hne, secondCopy G e f hne} := by
  by_cases heT : firstCopy G e f hne ∈ T
  · by_cases hfT : secondCopy G e f hne ∈ T
    · right; right; right
      ext i
      constructor
      · intro hi
        rcases copy_eq_first_or_second G e f hne i with rfl | rfl <;> simp
      · intro hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact heT
        · exact hfT
    · right; left
      ext i
      constructor
      · intro hi
        rcases copy_eq_first_or_second G e f hne i with rfl | rfl
        · simp
        · exact (hfT hi).elim
      · intro hi
        rw [mem_singleton] at hi
        subst i
        exact heT
  · by_cases hfT : secondCopy G e f hne ∈ T
    · right; right; left
      ext i
      constructor
      · intro hi
        rcases copy_eq_first_or_second G e f hne i with rfl | rfl
        · exact (heT hi).elim
        · simp
      · intro hi
        rw [mem_singleton] at hi
        subst i
        exact hfT
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      rcases copy_eq_first_or_second G e f hne i with rfl | rfl
      · exact heT hi
      · exact hfT hi


theorem activeSegmentFiber_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hactive
      (unitFlux d.graph e) := by
  let s := canonicalEdgeSegment d.graph e
  let p := s.toPath d.graph (d.active_supported s hactive)
  have hstart_ne_end : s.1 ≠ s.2.1 :=
    canonicalEdgeSegment_start_ne_end d.graph e
  have hcurrent :
      ofEdgeFun d.graph (unitFlux d.graph e) =
        fun g => if g = e.1 then 1 else 0 := by
    funext g
    unfold ofEdgeFun unitFlux
    split
    · rename_i hg
      by_cases hge : g = e.1
      · subst g
        simp
      · have hsub : (⟨g, hg⟩ : d.graph.edgeFinset) ≠ e := by
          intro h
          exact hge (congrArg Subtype.val h)
        simp [hge, hsub]
    · rename_i hg
      have hge : g ≠ e.1 := by
        intro h
        subst g
        exact hg e.2
      simp [hge]
  have hpedges : p.1.edges = [e.1] := by
    rw [show p.1.edges = s.2.2.1.edges from
      shb_AmbientSegment.toPath_edges d.graph s
        (d.active_supported s hactive)]
    change [s(e.1.out.1, e.1.out.2)] = [e.1]
    congr 1
    exact e.1.out_eq
  have hpbackbone : shb_IsBackboneOf d.graph
      (ofEdgeFun d.graph (unitFlux d.graph e)) s.1 s.2.1 p := by
    intro g hg
    rw [hpedges] at hg
    simp only [List.mem_singleton] at hg
    subst g
    rw [hcurrent]
    simp
  have hset : shb_backboneSet d.graph
      (ofEdgeFun d.graph (unitFlux d.graph e)) s.1 s.2.1 = {p} := by
    ext q
    rw [shb_mem_backboneSet]
    simp only [Finset.mem_singleton]
    constructor
    · intro hq
      have hedge_eq : ∀ g ∈ q.1.edges, g = e.1 := by
        intro g hg
        have hodd := hq g hg
        rw [hcurrent] at hodd
        by_contra hge
        simp [hge] at hodd
      have hqedges : q.1.edges = [e.1] := by
        cases hwalk : q.1.edges with
        | nil =>
            have hnil : q.1.Nil := SimpleGraph.Walk.edges_eq_nil.mp hwalk
            exact (hstart_ne_end hnil.eq).elim
        | cons g gs =>
            have hg : g = e.1 := hedge_eq g (by simp [hwalk])
            have hnodup : (g :: gs).Nodup := by
              rw [← hwalk]
              exact q.2.isTrail.edges_nodup
            have hgs : gs = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro x hx
              have hxe : x = e.1 := hedge_eq x (by
                rw [hwalk]
                exact List.mem_cons_of_mem g hx)
              rw [hxe] at hx
              exact (List.nodup_cons.mp (hg ▸ hnodup)).1 hx
            simp [hg, hgs]
      apply Subtype.ext
      apply SimpleGraph.Walk.edges_injective
      exact hqedges.trans hpedges.symm
    · rintro rfl
      exact hpbackbone
  refine ⟨sources_unitFlux d.graph e, ?_⟩
  change shb_backboneSelectSupport d.graph
      (ofEdgeFun d.graph (unitFlux d.graph e)) s.1 s.2.1 = some p
  unfold shb_backboneSelectSupport
  rw [hset]
  simp


theorem scan_after_unitFlux_none
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    scan.firstAdmissible
        (fun _ b => fluxBitConfig d.graph oddBit (unitFlux d.graph e) b)
        ⟨d, [e.1]⟩ = none := by
  unfold shb_DynamicEdgeExploration.firstAdmissible
  apply List.find?_eq_none.mpr
  intro b hb
  change b ∈ (d.graph.edgeFinset.erase e.1).toList at hb
  have hbErase : b ∈ d.graph.edgeFinset.erase e.1 :=
    Finset.mem_toList.mp hb
  have hbne : b ≠ e.1 := (Finset.mem_erase.mp hbErase).1
  have hbG : b ∈ d.graph.edgeFinset := (Finset.mem_erase.mp hbErase).2
  intro htrue
  change fluxBitConfig d.graph oddBit (unitFlux d.graph e) b = true at htrue
  unfold fluxBitConfig at htrue
  rw [dif_pos hbG] at htrue
  have hsub : (⟨b, hbG⟩ : d.graph.edgeFinset) ≠ e := by
    intro h
    exact hbne (congrArg Subtype.val h)
  simp [oddBit, unitFlux, hsub] at htrue


theorem program_complete_canonical_singleton_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    BackboneTwoEdgeBondProgram.program.CompleteEvent d
      [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
  constructor
  · simpa [BackboneTwoEdgeBondProgram.program,
      BackboneTwoEdgeBondProgram.encode, BondwiseSuffixEvent,
      edgeOfSegment?_canonicalEdgeSegment] using
      BackboneConcreteBondProgram.scan_firstAdmissible_unitFlux d e
  · have hterminal :
        canonicalEdgeSegment d.graph e ∈ d.active /\
        sources d.graph
            (boolCurrent (fluxBitConfig d.graph oddBit (unitFlux d.graph e))) =
          {(canonicalEdgeSegment d.graph e).1,
            (canonicalEdgeSegment d.graph e).2.1} /\
        scan.firstAdmissible
            (fun _ b => fluxBitConfig d.graph oddBit (unitFlux d.graph e) b)
            ⟨d, [e.1]⟩ = none := by
      refine ⟨hactive, ?_, scan_after_unitFlux_none d e⟩
      rw [sources_boolCurrent_oddBit]
      exact sources_unitFlux d.graph e
    simpa [BackboneTwoEdgeBondProgram.program,
      BackboneTwoEdgeBondProgram.encode, edgeOfSegment?_canonicalEdgeSegment,
      BondwiseSegmentProgram.TerminalEvent,
      BackboneTwoEdgeBondProgram.scan, BackboneTwoEdgeBondProgram.terminal,
      BackboneTwoEdgeBondProgram.boolSources,
      e.2] using hterminal


theorem secondEdge_mem_delete
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    f.1 ∈ (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
    canonicalEdgeSegment_edgeSet]
  refine ⟨SimpleGraph.mem_edgeFinset.mp f.2, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hfe
  exact hne (Subtype.ext hfe.symm)


end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
