/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part5
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

theorem sources_twoUnitFlux
    (G : SimpleGraph V) (e f : G.edgeFinset) :
    sources G (ofEdgeFun G (twoUnitFlux G e f)) =
      {(canonicalEdgeSegment G e).1,
          (canonicalEdgeSegment G e).2.1} ∆
        {(canonicalEdgeSegment G f).1,
          (canonicalEdgeSegment G f).2.1} := by
  unfold twoUnitFlux
  rw [← ofEdgeFun_add, sources_add,
    BackboneConcreteBondProgram.sources_unitFlux,
    BackboneConcreteBondProgram.sources_unitFlux]


theorem find?_eq_some_of_unique_true_mem
    {A : Type*} [DecidableEq A] (xs : List A) (a : A) (p : A -> Bool)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hp : ∀ x, x ∈ xs -> (p x = true <-> x = a)) :
    xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        simp [List.find?, (hp a (by simp)).mpr rfl]
      · have ha' : a ∈ xs := by simpa [Ne.symm hxa] using ha
        cases hpx : p x with
        | false =>
            simp only [List.find?, hpx]
            exact ih hnodup.2 ha' (fun y hy => hp y (by simp [hy]))
        | true => exact (hxa ((hp x (by simp)).mp hpx)).elim


theorem scan_secondAdmissible_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f) :
    scan.firstAdmissible
        (fun _ b => fluxBitConfig d.graph
          BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b)
        ⟨d, [e.1]⟩ = some f.1 := by
  unfold shb_DynamicEdgeExploration.firstAdmissible
  apply find?_eq_some_of_unique_true_mem
  · exact Finset.nodup_toList _
  · have hef : f.1 ≠ e.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    change f.1 ∈ (d.graph.edgeFinset.erase e.1).toList
    exact Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hef, f.2⟩)
  · intro b hb
    change b ∈ (d.graph.edgeFinset.erase e.1).toList at hb
    have hbErase : b ∈ d.graph.edgeFinset.erase e.1 :=
      Finset.mem_toList.mp hb
    have hbne : b ≠ e.1 := (Finset.mem_erase.mp hbErase).1
    have hbG : b ∈ d.graph.edgeFinset := (Finset.mem_erase.mp hbErase).2
    have hsube : (⟨b, hbG⟩ : d.graph.edgeFinset) ≠ e := by
      intro h
      exact hbne (congrArg Subtype.val h)
    constructor
    · intro hbit
      by_cases hsubf : (⟨b, hbG⟩ : d.graph.edgeFinset) = f
      · exact congrArg Subtype.val hsubf
      · change (if h : b ∈ d.graph.edgeFinset then
          BackboneConcreteBondProgram.oddBit
            (twoUnitFlux d.graph e f ⟨b, h⟩) else false) = true at hbit
        simp only [hbG, dite_true] at hbit
        simp [BackboneConcreteBondProgram.oddBit, twoUnitFlux,
          BackboneConcreteBondProgram.unitFlux, hsube, hsubf] at hbit
    · intro hbf
      subst b
      change (if h : f.1 ∈ d.graph.edgeFinset then
        BackboneConcreteBondProgram.oddBit
          (twoUnitFlux d.graph e f ⟨f.1, h⟩) else false) = true
      simp [f.2, BackboneConcreteBondProgram.oddBit, twoUnitFlux,
        BackboneConcreteBondProgram.unitFlux, hne.symm]


theorem program_complete_canonical_pair_twoUnitFlux
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
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  apply program_complete_pair_of_scan_data d (twoUnitFlux d.graph e f)
    (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) e f
  · exact edgeOfSegment?_canonicalEdgeSegment d e
  · exact edgeOfSegment?_canonicalEdgeSegment d f
  · exact hfirst
  · exact scan_secondAdmissible_twoUnitFlux d e f hne
  · exact fun h => hne (Subtype.ext h)
  · exact hactiveE
  · exact hactiveF
  · exact hpath
  · exact sources_twoUnitFlux d.graph e f


theorem selectorSpec_fiber_canonical_pair_twoUnitFlux
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
    (selectorSpec (V := V)).toPartialSelector.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
    hactiveE hactiveF hpath


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
