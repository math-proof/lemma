/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part5
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem scan_firstAdmissible_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    scan.firstAdmissible
        (fun _ f => fluxBitConfig d.graph oddBit (unitFlux d.graph e) f)
        ⟨d, none⟩ = some e.1 := by
  unfold shb_DynamicEdgeExploration.firstAdmissible
  apply find?_eq_some_of_unique_true
  · exact Finset.nodup_toList _
  · simpa [scan] using e.2
  · intro f
    constructor
    · intro hf
      change fluxBitConfig d.graph oddBit (unitFlux d.graph e) f = true at hf
      unfold fluxBitConfig at hf
      split at hf
      · rename_i hfg
        have heq : (⟨f, hfg⟩ : d.graph.edgeFinset) = e := by
          by_contra hne
          simp [oddBit, unitFlux, hne] at hf
        exact congrArg Subtype.val heq
      · simp at hf
    · intro hfe
      subst f
      change fluxBitConfig d.graph oddBit (unitFlux d.graph e) e.1 = true
      simp [fluxBitConfig, e.2, oddBit, unitFlux]


theorem sources_unitFlux
    (G : SimpleGraph V) (e : G.edgeFinset) :
    sources G (ofEdgeFun G (unitFlux G e)) =
      {(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} := by
  ext v
  rw [mem_sources]
  have hcurrent :
      ofEdgeFun G (unitFlux G e) = fun f => if f = e.1 then 1 else 0 := by
    funext f
    unfold ofEdgeFun unitFlux
    split
    · rename_i hf
      by_cases hfe : f = e.1
      · subst f
        simp
      · have hsub : (⟨f, hf⟩ : G.edgeFinset) ≠ e := by
          intro h
          exact hfe (congrArg Subtype.val h)
        simp [hfe, hsub]
    · rename_i hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hf e.2
      simp [hfe]
  rw [hcurrent]
  have hflux :
      incidentFlux G (fun f => if f = e.1 then 1 else 0) v =
        if v ∈ e.1 then 1 else 0 := by
    unfold incidentFlux
    by_cases hv : v ∈ e.1
    · rw [if_pos hv]
      simp [hv, e.2]
    · rw [if_neg hv]
      apply Finset.sum_eq_zero
      intro f hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hv (Finset.mem_filter.mp hf).2
      simp [hfe]
  rw [hflux]
  have hviff : v ∈ e.1 <-> v = e.1.out.1 ∨ v = e.1.out.2 := by
    calc
      v ∈ e.1 <-> v ∈ s(e.1.out.1, e.1.out.2) :=
        iff_of_eq (congrArg (fun z : Sym2 V => v ∈ z) e.1.out_eq).symm
      _ <-> v = e.1.out.1 ∨ v = e.1.out.2 := Sym2.mem_iff
  simp only [canonicalEdgeSegment, Finset.mem_insert, Finset.mem_singleton]
  by_cases hv : v ∈ e.1
  · rw [if_pos hv]
    exact ⟨fun _ => hviff.mp hv, fun _ => odd_one⟩
  · rw [if_neg hv]
    exact ⟨fun hodd => (by simp at hodd), fun hends => (hv (hviff.mpr hends)).elim⟩


theorem canonicalEdgeSegment_injective (G : SimpleGraph V) :
    Function.Injective (canonicalEdgeSegment G) := by
  intro e f hsegment
  have hedges := congrArg shb_AmbientSegment.edgeSet hsegment
  rw [canonicalEdgeSegment_edgeSet, canonicalEdgeSegment_edgeSet] at hedges
  exact Subtype.ext (Set.singleton_eq_singleton_iff.mp hedges)


@[simp] theorem edgeOfSegment?_canonicalEdgeSegment
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e := by
  unfold edgeOfSegment?
  split
  · rename_i hex
    have hchosen := Classical.choose_spec hex
    have heq : Classical.choose hex = e :=
      canonicalEdgeSegment_injective d.graph hchosen
    simp [heq]
  · rename_i hnone
    exact (hnone ⟨e, rfl⟩).elim


@[simp] theorem edgeOfSegment?_canonical
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e :=
  edgeOfSegment?_canonicalEdgeSegment d e


theorem program_complete_singleton_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
        canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph (ofEdgeFun d.graph m) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e)
          ⟨d, none⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e =>
      have hspec : canonicalEdgeSegment d.graph e = s :=
        edgeOfSegment?_eq_some_spec d s e hedge
      have hterminal :
          canonicalEdgeSegment d.graph e ∈ d.active /\
            sources d.graph
                (boolCurrent (fluxBitConfig d.graph oddBit m)) =
              {(canonicalEdgeSegment d.graph e).1,
                (canonicalEdgeSegment d.graph e).2.1} := by
        simpa [program, encode, hedge, BondwiseSegmentProgram.TerminalEvent,
          scan, terminal, boolSources, e.2] using h.2
      refine ⟨e, hspec, hterminal.1, ?_⟩
      rw [← sources_boolCurrent_oddBit d.graph m]
      exact hterminal.2


theorem program_complete_singleton_data_with_scan
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      scan.firstAdmissible
          (fun _ f => fluxBitConfig d.graph oddBit m f) ⟨d, none⟩ =
          some e.1 /\
        canonicalEdgeSegment d.graph e = s /\
          canonicalEdgeSegment d.graph e ∈ d.active /\
            sources d.graph (ofEdgeFun d.graph m) =
              {(canonicalEdgeSegment d.graph e).1,
                (canonicalEdgeSegment d.graph e).2.1} := by
  obtain ⟨e, hsegment, hactive, hsources⟩ :=
    program_complete_singleton_data d m s h
  have hencode : edgeOfSegment? d s = some e := by
    rw [← hsegment]
    exact edgeOfSegment?_canonicalEdgeSegment d e
  have hfirst : scan.firstAdmissible
      (fun _ f => fluxBitConfig d.graph oddBit m f) ⟨d, none⟩ =
      some e.1 := by
    simpa [program, encode, hencode, BondwiseSuffixEvent] using h.1
  exact ⟨e, hfirst, hsegment, hactive, hsources⟩


theorem scan_selects_length_le_one
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool)
    (bonds : List (Sym2 V))
    (hselect : scan.Selects (fun _ e => omega e) ⟨d, none⟩ bonds) :
    bonds.length <= 1 := by
  cases bonds with
  | nil => simp
  | cons accepted rest =>
      cases rest with
      | nil => simp
      | cons next tail =>
          have hnext := hselect.2.1
          simp [scan, shb_DynamicEdgeExploration.firstAdmissible] at hnext


theorem program_complete_word_eq_nil_or_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] \/ ∃ s, word = [s] := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil => exact Or.inr ⟨s, rfl⟩
      | cons t tail =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e)
              ⟨d, none⟩ = some s(s.1, s.1) := by
            simpa [program, encode, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim


theorem program_complete_cons_tail_eq_nil
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : ss = [] := by
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) h with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · simpa using congrArg List.tail hsingleton


theorem edgeOfSegment?_eq_some_of_program_complete_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset, edgeOfSegment? d s = some e := by
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e)
          ⟨d, none⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e => exact ⟨e, rfl⟩


theorem program_complete_singleton_injective
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (hs : program.CompleteEvent d [s] m)
    (ht : program.CompleteEvent d [t] m) :
    s = t := by
  obtain ⟨es, hedgeS⟩ :=
    edgeOfSegment?_eq_some_of_program_complete_singleton d m s hs
  obtain ⟨et, hedgeT⟩ :=
    edgeOfSegment?_eq_some_of_program_complete_singleton d m t ht
  have hses := edgeOfSegment?_eq_some_spec d s es hedgeS
  have htet := edgeOfSegment?_eq_some_spec d t et hedgeT
  have hselectS :
      scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, none⟩ =
        some es.1 := by
    simpa [program, encode, hedgeS, BondwiseSuffixEvent] using hs.1
  have hselectT :
      scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, none⟩ =
        some et.1 := by
    simpa [program, encode, hedgeT, BondwiseSuffixEvent] using ht.1
  have he : es.1 = et.1 := Option.some.inj (hselectS.symm.trans hselectT)
  have hesub : es = et := Subtype.ext he
  exact hses.symm.trans (hesub ▸ htet)


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
