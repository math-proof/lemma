/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
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

theorem fin3_first_scan_cases : fin3LeftFirst ∨ fin3RightFirst := by
  let admissible : State (Fin 3) -> Sym2 (Fin 3) -> Bool :=
    fun _ b => fluxBitConfig fin3PathDomain.graph
      BackboneConcreteBondProgram.oddBit fin3PathFlux b
  cases hresult : scan.firstAdmissible admissible
      ⟨fin3PathDomain, []⟩ with
  | none =>
      have hfind :
          fin3PathDomain.graph.edgeFinset.1.toList.find?
              (admissible ⟨fin3PathDomain, []⟩) = none := by
        simpa [shb_DynamicEdgeExploration.firstAdmissible, scan]
          using hresult
      have hleftMem :
          fin3LeftEdge.1 ∈ fin3PathDomain.graph.edgeFinset.1.toList :=
        Finset.mem_toList.mpr fin3LeftEdge.2
      have hleftTrue :
          admissible ⟨fin3PathDomain, []⟩ fin3LeftEdge.1 = true := by
        unfold admissible fluxBitConfig
        have hmemDomain :
            fin3LeftEdge.1 ∈ fin3PathDomain.graph.edgeFinset :=
          fin3LeftEdge.2
        rw [dif_pos hmemDomain]
        change BackboneConcreteBondProgram.oddBit
          (fin3PathFlux fin3LeftEdge) = true
        rw [BackboneConcreteBondProgram.oddBit_eq_true_iff]
        change Odd
          (BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3LeftEdge fin3LeftEdge +
            BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3RightEdge fin3LeftEdge)
        rw [show BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3LeftEdge fin3LeftEdge = 1 by
            simp [BackboneConcreteBondProgram.unitFlux],
          show BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3RightEdge fin3LeftEdge = 0 by
            simp [BackboneConcreteBondProgram.unitFlux,
              fin3LeftEdge_ne_rightEdge]]
        exact odd_one
      exact ((List.find?_eq_none.mp hfind) fin3LeftEdge.1
        hleftMem hleftTrue).elim
  | some edge =>
      have hedgeMem := scan.firstAdmissible_mem admissible
        ⟨fin3PathDomain, []⟩ edge hresult
      have hedgeList :
          edge ∈ fin3PathDomain.graph.edgeFinset.1.toList := by
        simpa [scan] using hedgeMem
      have hedgeGraph : edge ∈ fin3PathGraph.edgeFinset := by
        exact Finset.mem_toList.mp hedgeList
      rw [fin3PathGraph_edgeFinset] at hedgeGraph
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedgeGraph
      rcases hedgeGraph with hedge | hedge
      · left
        unfold fin3LeftFirst
        simpa [admissible, hedge] using hresult
      · right
        unfold fin3RightFirst
        simpa [admissible, hedge] using hresult


theorem fin3_first_scan_exclusive : ¬(fin3LeftFirst ∧ fin3RightFirst) := by
  rintro ⟨hleft, hright⟩
  have hedge : fin3LeftEdge.1 = fin3RightEdge.1 :=
    Option.some.inj (hleft.symm.trans hright)
  exact fin3LeftEdge_ne_rightEdge (Subtype.ext hedge)


theorem fin3LeftEdge_out_cases :
    fin3LeftEdge.1.out = ((0 : Fin 3), 1) ∨
      fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
  have hout := fin3LeftEdge.1.out_eq
  change s(fin3LeftEdge.1.out.1, fin3LeftEdge.1.out.2) =
    s((0 : Fin 3), 1) at hout
  rw [Sym2.eq, Sym2.rel_iff] at hout
  rcases hout with h | h
  · exact Or.inl (Prod.ext h.1 h.2)
  · exact Or.inr (Prod.ext h.1 h.2)


theorem fin3RightEdge_out_cases :
    fin3RightEdge.1.out = ((1 : Fin 3), 2) ∨
      fin3RightEdge.1.out = ((2 : Fin 3), 1) := by
  have hout := fin3RightEdge.1.out_eq
  change s(fin3RightEdge.1.out.1, fin3RightEdge.1.out.2) =
    s((1 : Fin 3), 2) at hout
  rw [Sym2.eq, Sym2.rel_iff] at hout
  rcases hout with h | h
  · exact Or.inl (Prod.ext h.1 h.2)
  · exact Or.inr (Prod.ext h.1 h.2)


theorem fin3_forward_path_iff :
    FormsTwoEdgePath
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge) <->
      fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\
        fin3RightEdge.1.out = ((1 : Fin 3), 2) := by
  rcases fin3LeftEdge_out_cases with hleft | hleft <;>
    rcases fin3RightEdge_out_cases with hright | hright <;>
    simp [FormsTwoEdgePath, canonicalEdgeSegment, hleft, hright]


theorem fin3_reverse_path_iff :
    FormsTwoEdgePath
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) <->
      fin3RightEdge.1.out = ((2 : Fin 3), 1) /\
        fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
  rcases fin3LeftEdge_out_cases with hleft | hleft <;>
    rcases fin3RightEdge_out_cases with hright | hright <;>
    simp [FormsTwoEdgePath, canonicalEdgeSegment, hleft, hright]


theorem fin3_forward_fiber_iff :
    (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
        [canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
          canonicalEdgeSegment fin3PathGraph fin3RightEdge]
        fin3PathFlux <->
      fin3LeftFirst /\
        FormsTwoEdgePath
          (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
          (canonicalEdgeSegment fin3PathGraph fin3RightEdge) := by
  constructor
  · intro hfiber
    rw [(selectorSpec (V := Fin 3)).fiber_iff_completeEvent] at hfiber
    obtain ⟨e, f, he, hf, hfirst, _, _, _, _, hpath, _⟩ :=
      program_complete_pair_data fin3PathDomain fin3PathFlux
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge) hfiber
    have heq : e = fin3LeftEdge :=
      canonicalEdgeSegment_injective fin3PathGraph he
    have hfeq : f = fin3RightEdge :=
      canonicalEdgeSegment_injective fin3PathGraph hf
    subst e
    subst f
    exact ⟨hfirst, hpath⟩
  · rintro ⟨hfirst, hpath⟩
    exact selectorSpec_fiber_canonical_pair_twoUnitFlux
      fin3PathDomain fin3LeftEdge fin3RightEdge
      fin3LeftEdge_ne_rightEdge hfirst fin3LeftEdge_active
      fin3RightEdge_active hpath


theorem fin3_reverse_fiber_iff :
    (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
        [canonicalEdgeSegment fin3PathGraph fin3RightEdge,
          canonicalEdgeSegment fin3PathGraph fin3LeftEdge]
        fin3PathFlux <->
      fin3RightFirst /\
        FormsTwoEdgePath
          (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
          (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) := by
  constructor
  · intro hfiber
    rw [(selectorSpec (V := Fin 3)).fiber_iff_completeEvent] at hfiber
    obtain ⟨e, f, he, hf, hfirst, _, _, _, _, hpath, _⟩ :=
      program_complete_pair_data fin3PathDomain fin3PathFlux
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) hfiber
    have heq : e = fin3RightEdge :=
      canonicalEdgeSegment_injective fin3PathGraph he
    have hfeq : f = fin3LeftEdge :=
      canonicalEdgeSegment_injective fin3PathGraph hf
    subst e
    subst f
    exact ⟨hfirst, hpath⟩
  · rintro ⟨hfirst, hpath⟩
    have hfluxSwap :
        twoUnitFlux fin3PathDomain.graph fin3RightEdge fin3LeftEdge =
          fin3PathFlux := by
      funext g
      simp [fin3PathFlux, twoUnitFlux, Nat.add_comm]
    have hfirst' :
        scan.firstAdmissible
            (fun _ b => fluxBitConfig fin3PathDomain.graph
              BackboneConcreteBondProgram.oddBit
                (twoUnitFlux fin3PathDomain.graph
                  fin3RightEdge fin3LeftEdge) b)
            ⟨fin3PathDomain, []⟩ = some fin3RightEdge.1 := by
      rw [hfluxSwap]
      exact hfirst
    have hfiber := selectorSpec_fiber_canonical_pair_twoUnitFlux
      fin3PathDomain fin3RightEdge fin3LeftEdge
      fin3LeftEdge_ne_rightEdge.symm
      hfirst'
      fin3RightEdge_active fin3LeftEdge_active hpath
    rw [hfluxSwap] at hfiber
    exact hfiber


theorem fin3_twoSegment_fiber_iff_orientation_and_scan :
    ((selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
          [canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
            canonicalEdgeSegment fin3PathGraph fin3RightEdge]
          fin3PathFlux ∨
        (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
          [canonicalEdgeSegment fin3PathGraph fin3RightEdge,
            canonicalEdgeSegment fin3PathGraph fin3LeftEdge]
          fin3PathFlux) <->
      (fin3LeftFirst /\
          fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\
          fin3RightEdge.1.out = ((1 : Fin 3), 2)) ∨
        (fin3RightFirst /\
          fin3RightEdge.1.out = ((2 : Fin 3), 1) /\
          fin3LeftEdge.1.out = ((1 : Fin 3), 0)) := by
  rw [fin3_forward_fiber_iff, fin3_reverse_fiber_iff,
    fin3_forward_path_iff, fin3_reverse_path_iff]


theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector := by
  exact ⟨selectorSpec (V := V), fun _ _ _ => Iff.rfl⟩


theorem selectorSpec_nonempty_canonicalCertificate_iff_toggleExists
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    Nonempty (AsymmetricBondwiseCoordinateCertificate
      ((program (V := V)).runSpec d (s :: ss))
      (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs)
      ((program (V := V)).liftedResidualRunSpec d s ss)
      (selectorSpec (V := V)).toPartialSelector beta J d s ss hs) <->
      (selectorSpec (V := V)).CanonicalBondwiseToggleExists
        beta J d s ss hs :=
  (selectorSpec (V := V)).nonempty_canonicalCertificate_iff_toggleExists
    beta J d s ss hs


theorem selectorSpec_canonicalToggleExists_of_componentwise
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : (selectorSpec (V := V)).CanonicalComponentwiseToggleExists
      beta J d s ss hs) :
    (selectorSpec (V := V)).CanonicalBondwiseToggleExists
      beta J d s ss hs :=
  (selectorSpec (V := V)).canonicalToggleExists_of_componentwise
    beta J d s ss hs h

end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
