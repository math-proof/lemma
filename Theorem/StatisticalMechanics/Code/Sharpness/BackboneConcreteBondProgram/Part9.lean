/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem SelectorRealization.programRealizes
    {P : BondwiseSegmentProgram V}
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization P S) : ProgramRealizes P S := by
  refine ⟨R.toCompleteSpec, ?_⟩
  intro d word m
  exact (R.toCompleteSpec.fiber_iff_completeEvent d word m).trans
    (R.complete_iff_fiber d word m)


theorem nonempty_selectorRealization_iff_programRealizes
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) :
    Nonempty (SelectorRealization P S) <-> ProgramRealizes P S := by
  constructor
  · rintro ⟨R⟩
    exact R.programRealizes
  · rintro ⟨R, hrealizes⟩
    refine ⟨⟨?_⟩⟩
    intro d word m
    exact (R.fiber_iff_completeEvent d word m).symm.trans
      (hrealizes d word m)


theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector := by
  exact ⟨selectorSpec (V := V), fun _ _ _ => Iff.rfl⟩


theorem program_not_realizes_of_two_segment_fiber
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (hfiber : S.Fiber d (s :: t :: ss) m) :
    ¬ProgramRealizes (program (V := V)) S := by
  rintro ⟨R, hrealizes⟩
  have hcomplete : program.CompleteEvent d (s :: t :: ss) m :=
    (R.fiber_iff_completeEvent d (s :: t :: ss) m).mp
      ((hrealizes d (s :: t :: ss) m).mpr hfiber)
  rcases program_complete_word_eq_nil_or_singleton d m (s :: t :: ss)
      hcomplete with hnil | ⟨u, hsingleton⟩
  · simp at hnil
  · simp at hsingleton


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

end BackboneConcreteBondProgram
end
end StatMech.Sharpness
