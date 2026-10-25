/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part10
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


set_option maxHeartbeats 800000 in


theorem CompleteBondwiseSelectorSpec.path_sources_of_canonical_toggle
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
        stepToggleSource R.toPartialSelector d s ss := by
  intro m hm
  change PairContributes d.graph beta J m
    (R.toPartialSelector.sourceClass d (s :: ss))
    (stepToggleSource R.toPartialSelector d s ss)
    (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs)
    (liftedResidualFiber R.toPartialSelector d s ss) at hm
  rcases hm with hleft | hright
  · obtain ⟨T, hTsrc, hfull, hvacuum⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss))
          (R.toPartialSelector.Fiber d (s :: ss))
          (liftedResidualVacuum d s) hleft
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m T :=
      ⟨(R.fiber_iff_runSpec_event d (s :: ss)
          (profileFlux d.graph m T)).mp hfull,
        (residualVacuumRunSpec_event d s
          (profileFlux d.graph m (univ \ T))).mpr hvacuum⟩
    have hrightPair := (bondwise_toggle m (Or.inl hleft) T).mp hleftPair
    have hhead : shb_ActiveSegmentFiber d s hs
        (profileFlux d.graph m (T ∆ path m (Or.inl hleft))) :=
      (activeSegmentRunSpec_event d s hs _).mp hrightPair.1
    have htoggleSrc :
        RandomCurrent.sources (endsM d.graph m)
            (T ∆ path m (Or.inl hleft)) = {s.1, s.2.1} :=
      (FluxEdgeCopy.sources_eq d.graph m _).trans hhead.1
    rw [RandomCurrent.sources_symmDiff, hTsrc] at htoggleSrc
    change RandomCurrent.sources (endsM d.graph m)
        (path m (Or.inl hleft)) =
      R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1}
    calc
      RandomCurrent.sources (endsM d.graph m) (path m (Or.inl hleft)) =
          R.toPartialSelector.sourceClass d (s :: ss) ∆
            (R.toPartialSelector.sourceClass d (s :: ss) ∆
              RandomCurrent.sources (endsM d.graph m)
                (path m (Or.inl hleft))) := by simp
      _ = R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1} :=
        congrArg (fun U =>
          R.toPartialSelector.sourceClass d (s :: ss) ∆ U) htoggleSrc
  · obtain ⟨T, hTsrc, hhead, hresidual⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss) ∆
            stepToggleSource R.toPartialSelector d s ss)
          (shb_ActiveSegmentFiber d s hs)
          (liftedResidualFiber R.toPartialSelector d s ss) hright
    let hmRight : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m := Or.inr hright
    let togglePath : Finset (Copy d.graph m) := path m hmRight
    have hrightPair : BondwisePairEvent (activeSegmentRunSpec d s hs)
        (P.liftedResidualRunSpec d s ss) d.graph m T :=
      ⟨(activeSegmentRunSpec_event d s hs
          (profileFlux d.graph m T)).mpr hhead,
        (P.liftedResidualRunSpec_event d s ss
          (profileFlux d.graph m (univ \ T))).mpr
            ((R.liftedResidualFiber_iff_liftedRunEvent d s ss _).mp
              hresidual)⟩
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m
          (T ∆ togglePath) := by
      have htoggle :=
        (bondwise_toggle m hmRight (T ∆ togglePath)).mpr
      have hcancel : T ∆ togglePath ∆ path m hmRight = T := by
        simp only [togglePath, symmDiff_symmDiff_cancel_right]
      rw [hcancel] at htoggle
      exact htoggle hrightPair
    have hfull : R.toPartialSelector.Fiber d (s :: ss)
        (profileFlux d.graph m (T ∆ togglePath)) :=
      (R.fiber_iff_runSpec_event d (s :: ss) _).mpr hleftPair.1
    have htoggleSrc :
        RandomCurrent.sources (endsM d.graph m)
            (T ∆ togglePath) =
          R.toPartialSelector.sourceClass d (s :: ss) :=
      (FluxEdgeCopy.sources_eq d.graph m _).trans
        (R.toPartialSelector.sources_eq_sourceClass_of_select d _ _ hfull)
    have hTsrc' : RandomCurrent.sources (endsM d.graph m) T =
        {s.1, s.2.1} := by
      simpa [stepToggleSource, symmDiff_assoc] using hTsrc
    rw [RandomCurrent.sources_symmDiff, hTsrc'] at htoggleSrc
    change RandomCurrent.sources (endsM d.graph m) togglePath =
      R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1}
    calc
      RandomCurrent.sources (endsM d.graph m) togglePath =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆ RandomCurrent.sources (endsM d.graph m)
              togglePath) := by simp
      _ = {s.1, s.2.1} ∆
          R.toPartialSelector.sourceClass d (s :: ss) :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) htoggleSrc
      _ = R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1} :=
        symmDiff_comm _ _


theorem CompleteBondwiseSelectorSpec.exists_canonical_rightPair_of_contributes
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m) :
    ∃ T, BondwisePairEvent (activeSegmentRunSpec d s hs)
      (P.liftedResidualRunSpec d s ss) d.graph m T := by
  change PairContributes d.graph beta J m
    (R.toPartialSelector.sourceClass d (s :: ss))
    (stepToggleSource R.toPartialSelector d s ss)
    (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs)
    (liftedResidualFiber R.toPartialSelector d s ss) at hm
  rcases hm with hleft | hright
  · obtain ⟨T, _, hfull, hvacuum⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss))
          (R.toPartialSelector.Fiber d (s :: ss))
          (liftedResidualVacuum d s) hleft
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m T :=
      ⟨(R.fiber_iff_runSpec_event d (s :: ss)
          (profileFlux d.graph m T)).mp hfull,
        (residualVacuumRunSpec_event d s
          (profileFlux d.graph m (univ \ T))).mpr hvacuum⟩
    exact ⟨T ∆ path m (Or.inl hleft),
      (bondwise_toggle m (Or.inl hleft) T).mp hleftPair⟩
  · obtain ⟨T, _, hhead, hresidual⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss) ∆
            stepToggleSource R.toPartialSelector d s ss)
          (shb_ActiveSegmentFiber d s hs)
          (liftedResidualFiber R.toPartialSelector d s ss) hright
    refine ⟨T, ?_⟩
    exact ⟨(activeSegmentRunSpec_event d s hs
        (profileFlux d.graph m T)).mpr hhead,
      (P.liftedResidualRunSpec_event d s ss
        (profileFlux d.graph m (univ \ T))).mpr
          ((R.liftedResidualFiber_iff_liftedRunEvent d s ss _).mp
            hresidual)⟩


theorem CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_right_invariant
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (right_invariant : ∀ T,
      BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    stepToggleSource R.toPartialSelector d s ss = ∅ := by
  obtain ⟨T, hright⟩ := R.exists_canonical_rightPair_of_contributes
    beta J d s ss hs path bondwise_toggle m hm
  have hrightToggle := (right_invariant T).mp hright
  have hsrc : RandomCurrent.sources (endsM d.graph m) T = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m T).trans
      ((activeSegmentRunSpec_event d s hs _).mp hright.1).1
  have hsrcToggle : RandomCurrent.sources (endsM d.graph m)
      (T ∆ path m hm) = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m _).trans
      ((activeSegmentRunSpec_event d s hs _).mp hrightToggle.1).1
  rw [RandomCurrent.sources_symmDiff, hsrc] at hsrcToggle
  have hpathEmpty :
      RandomCurrent.sources (endsM d.graph m) (path m hm) = ∅ := by
    calc
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆
              RandomCurrent.sources (endsM d.graph m) (path m hm)) := by simp
      _ = {s.1, s.2.1} ∆ {s.1, s.2.1} :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) hsrcToggle
      _ = ∅ := symmDiff_self _
  exact (R.path_sources_of_canonical_toggle
    beta J d s ss hs path bondwise_toggle m hm).symm.trans hpathEmpty


theorem CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_activeHead_outsideCut
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (cut : Set (Sym2 V))
    (hpath : SupportedInCut d.graph m cut (path m hm))
    (hhead : FluxEventOutsideCut d.graph m cut
      ((activeSegmentRunSpec d s hs).Event d.graph)) :
    stepToggleSource R.toPartialSelector d s ss = ∅ := by
  obtain ⟨T, hright⟩ := R.exists_canonical_rightPair_of_contributes
    beta J d s ss hs path bondwise_toggle m hm
  have hheadToggle := (fluxEvent_toggle_iff d.graph m cut
    ((activeSegmentRunSpec d s hs).Event d.graph) hhead
      T (path m hm) hpath).mp hright.1
  have hsrc : RandomCurrent.sources (endsM d.graph m) T = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m T).trans
      ((activeSegmentRunSpec_event d s hs _).mp hright.1).1
  have hsrcToggle : RandomCurrent.sources (endsM d.graph m)
      (T ∆ path m hm) = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m _).trans
      ((activeSegmentRunSpec_event d s hs _).mp hheadToggle).1
  rw [RandomCurrent.sources_symmDiff, hsrc] at hsrcToggle
  have hpathEmpty :
      RandomCurrent.sources (endsM d.graph m) (path m hm) = ∅ := by
    calc
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆
              RandomCurrent.sources (endsM d.graph m) (path m hm)) := by simp
      _ = {s.1, s.2.1} ∆ {s.1, s.2.1} :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) hsrcToggle
      _ = ∅ := symmDiff_self _
  exact (R.path_sources_of_canonical_toggle
    beta J d s ss hs path bondwise_toggle m hm).symm.trans hpathEmpty


theorem CompleteBondwiseSelectorSpec.not_activeHead_outsideCut_of_toggleSource_ne_empty
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (cut : Set (Sym2 V))
    (hpath : SupportedInCut d.graph m cut (path m hm))
    (hsource : stepToggleSource R.toPartialSelector d s ss ≠ ∅) :
    ¬ FluxEventOutsideCut d.graph m cut
      ((activeSegmentRunSpec d s hs).Event d.graph) := by
  intro hhead
  exact hsource (R.stepToggleSource_eq_empty_of_activeHead_outsideCut
    beta J d s ss hs path bondwise_toggle m hm cut hpath hhead)


end BackboneConcreteSelector
end
end StatMech.Sharpness
