import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneConcreteSelector


/--
[BondwiseSuffixSpec.toRunSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma toRunSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {E : BondwiseSuffixSpec V}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (m : G.edgeFinset -> Nat) :
-- imply
  E.toRunSpec.Event G m <-> E.Event G m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseSuffixSpec.toRunSpec_event E G m

/--
[BondwiseRunSpec.ofPredicate_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma ofPredicate_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (Q : (G.edgeFinset -> Nat) -> Prop)
  (m : G.edgeFinset -> Nat) :
-- imply
  (BondwiseRunSpec.ofPredicate G Q).Event G m <-> Q m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseRunSpec.ofPredicate_event G Q m

/--
[BondwiseRunToggleCovariance.refl_of_outsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma refl_of_outsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {E : BondwiseRunSpec V}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {path : Finset (Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (hpath : SupportedInCut G m cut path)
  (hE : FluxEventOutsideCut G m cut (E.Event G)) :
-- imply
  BondwiseRunToggleCovariance E E G m path := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseRunToggleCovariance.refl_of_outsideCut E G m cut path hpath hE

/--
[BondwisePairEvent.toggle_iff_of_componentwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma toggle_iff_of_componentwise_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {left₁ left₂ right₁ right₂ : BondwiseRunSpec V}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {path : Finset (Copy G m)}
  {T : Finset (Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (h₁ : BondwiseRunToggleCovariance left₁ right₁ G m path)
  (h₂ : BondwiseRunToggleCovariance left₂ right₂ G m path) :
-- imply
  BondwisePairEvent left₁ left₂ G m T <-> BondwisePairEvent right₁ right₂ G m (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwisePairEvent.toggle_iff_of_componentwise left₁ left₂ right₁ right₂ G m path h₁ h₂ T

/--
[BondwisePairEvent.toggle_iff_of_outsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma toggle_iff_of_outsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {E₁ E₂ : BondwiseRunSpec V}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {path : Finset (Copy G m)}
  {T : Finset (Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (hpath : SupportedInCut G m cut path)
  (h₁ : FluxEventOutsideCut G m cut (E₁.Event G))
  (h₂ : FluxEventOutsideCut G m cut (E₂.Event G)) :
-- imply
  BondwisePairEvent E₁ E₂ G m T <-> BondwisePairEvent E₁ E₂ G m (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwisePairEvent.toggle_iff_of_outsideCut E₁ E₂ G m cut path hpath h₁ h₂ T

/--
[AsymmetricBondwiseCoordinateCertificate.actualMass_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma actualMass_active_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {left₁ left₂ right₁ right₂ : BondwiseRunSpec V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {R : AsymmetricBondwiseCoordinateCertificate left₁ left₂ right₁ right₂ S beta J d s ss hs}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.AsymmetricBondwiseCoordinateCertificate.actualMass_active left₁ left₂ right₁ right₂ S beta J d s ss hs R

/--
[BondwiseSegmentProgram.suffixSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma suffixSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  (P.suffixSpec d word).Event d.graph m = BondwiseSuffixEvent d.graph P.scan (P.initial d) (P.encode d word) P.bit m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseSegmentProgram.suffixSpec_event P d word m

/--
[BondwiseSegmentProgram.runSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma runSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  (P.runSpec d word).Event d.graph m <-> P.CompleteEvent d word m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseSegmentProgram.runSpec_event P d word m

/--
[CompleteBondwiseSelectorSpec.fiber_iff_runSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma fiber_iff_runSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  R.toPartialSelector.Fiber d word m <-> (P.runSpec d word).Event d.graph m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.fiber_iff_runSpec_event R d word m

/--
[residualVacuumRunSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma residualVacuumRunSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  (residualVacuumRunSpec d s).Event d.graph m <-> liftedResidualVacuum d s m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.residualVacuumRunSpec_event d s m

/--
[activeSegmentRunSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma activeSegmentRunSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (hs : s ∈ d.active)
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  (activeSegmentRunSpec d s hs).Event d.graph m <-> shb_ActiveSegmentFiber d s hs m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.activeSegmentRunSpec_event d s hs m

/--
[BondwiseSegmentProgram.liftedResidualRunSpec_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma liftedResidualRunSpec_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  (P.liftedResidualRunSpec d s word).Event d.graph m <-> P.LiftedRunEvent d s word m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseSegmentProgram.liftedResidualRunSpec_event P d s word m

/--
[CompleteBondwiseSelectorSpec.liftedResidualFiber_iff_liftedRunEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma liftedResidualFiber_iff_liftedRunEvent_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (q : d.graph.edgeFinset -> Nat) :
-- imply
  liftedResidualFiber R.toPartialSelector d s word q <-> P.LiftedRunEvent d s word q := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.liftedResidualFiber_iff_liftedRunEvent R d s word q

/--
[CompleteBondwiseSelectorSpec.leftPairNormalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma leftPairNormalForm_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {vacuum : BondwiseRunSpec V}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {T : Finset (Copy d.graph m)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hvacuum : liftedResidualVacuum d s (profileFlux d.graph m (univ \ T)) <-> vacuum.Event d.graph (profileFlux d.graph m (univ \ T))) :
-- imply
  (R.toPartialSelector.Fiber d (s :: ss) (profileFlux d.graph m T) /\ liftedResidualVacuum d s (profileFlux d.graph m (univ \ T))) <-> BondwisePairEvent (P.runSpec d (s :: ss)) vacuum d.graph m T := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.leftPairNormalForm R vacuum d s ss m T hvacuum

/--
[CompleteBondwiseSelectorSpec.rightPairNormalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma rightPairNormalForm_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {T : Finset (Copy d.graph m)}
-- given
  (head residual : BondwiseRunSpec V)
  (hs : s ∈ d.active)
  (m : d.graph.edgeFinset -> Nat)
  (hhead : shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) <-> head.Event d.graph (profileFlux d.graph m T))
  (hresidual : P.LiftedRunEvent d s ss (profileFlux d.graph m (univ \ T)) <-> residual.Event d.graph (profileFlux d.graph m (univ \ T))) :
-- imply
  (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\ liftedResidualFiber R.toPartialSelector d s ss (profileFlux d.graph m (univ \ T))) <-> BondwisePairEvent head residual d.graph m T := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.rightPairNormalForm R head residual d s ss hs m T hhead hresidual

/--
[CompleteBondwiseSelectorSpec.path_sources_of_canonical_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma path_sources_of_canonical_toggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (R.toPartialSelector.sourceClass d (s :: ss)) (stepToggleSource R.toPartialSelector d s ss) (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber R.toPartialSelector d s ss)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (bondwise_toggle : ∀ m (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) T, BondwisePairEvent (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
-- imply
  ∀ m hm, RandomCurrent.sources (endsM d.graph m) (path m hm) = stepToggleSource R.toPartialSelector d s ss := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.path_sources_of_canonical_toggle R beta J d s ss hs path bondwise_toggle

/--
[CompleteBondwiseSelectorSpec.exists_canonical_rightPair_of_contributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma exists_canonical_rightPair_of_contributes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (R.toPartialSelector.sourceClass d (s :: ss)) (stepToggleSource R.toPartialSelector d s ss) (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber R.toPartialSelector d s ss)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (bondwise_toggle : ∀ m (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) T, BondwisePairEvent (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) :
-- imply
  ∃ T, BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m T := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.exists_canonical_rightPair_of_contributes R beta J d s ss hs path bondwise_toggle m hm

/--
[CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_right_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma stepToggleSource_eq_empty_of_right_invariant_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (R.toPartialSelector.sourceClass d (s :: ss)) (stepToggleSource R.toPartialSelector d s ss) (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber R.toPartialSelector d s ss)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (bondwise_toggle : ∀ m (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) T, BondwisePairEvent (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m)
  (right_invariant : ∀ T, BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
-- imply
  stepToggleSource R.toPartialSelector d s ss = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_right_invariant R beta J d s ss hs path bondwise_toggle m hm right_invariant

/--
[CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_activeHead_outsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma stepToggleSource_eq_empty_of_activeHead_outsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (R.toPartialSelector.sourceClass d (s :: ss)) (stepToggleSource R.toPartialSelector d s ss) (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber R.toPartialSelector d s ss)}
  {cut : Set (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (bondwise_toggle : ∀ m (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) T, BondwisePairEvent (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m)
  (hpath : SupportedInCut d.graph m cut (path m hm))
  (hhead : FluxEventOutsideCut d.graph m cut ((activeSegmentRunSpec d s hs).Event d.graph)) :
-- imply
  stepToggleSource R.toPartialSelector d s ss = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_activeHead_outsideCut R beta J d s ss hs path bondwise_toggle m hm cut hpath hhead

/--
[CompleteBondwiseSelectorSpec.not_activeHead_outsideCut_of_toggleSource_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma not_activeHead_outsideCut_of_toggleSource_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (R.toPartialSelector.sourceClass d (s :: ss)) (stepToggleSource R.toPartialSelector d s ss) (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber R.toPartialSelector d s ss)}
  {cut : Set (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (bondwise_toggle : ∀ m (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m) T, BondwisePairEvent (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes R.toPartialSelector beta J d s ss hs m)
  (hpath : SupportedInCut d.graph m cut (path m hm))
  (hsource : stepToggleSource R.toPartialSelector d s ss ≠ ∅) :
-- imply
  ¬ FluxEventOutsideCut d.graph m cut ((activeSegmentRunSpec d s hs).Event d.graph) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.not_activeHead_outsideCut_of_toggleSource_ne_empty R beta J d s ss hs path bondwise_toggle m hm cut hpath hsource

/--
[CompleteBondwiseSelectorSpec.canonicalToggleExists_of_componentwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma canonicalToggleExists_of_componentwise_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (h : R.CanonicalComponentwiseToggleExists beta J d s ss hs) :
-- imply
  R.CanonicalBondwiseToggleExists beta J d s ss hs := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.canonicalToggleExists_of_componentwise R beta J d s ss hs h

/--
[CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma nonempty_canonicalCertificate_iff_toggleExists_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  Nonempty (AsymmetricBondwiseCoordinateCertificate (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss) R.toPartialSelector beta J d s ss hs) <-> R.CanonicalBondwiseToggleExists beta J d s ss hs := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists R beta J d s ss hs

/--
[CompleteBondwiseSelectorSpec.not_toggleExists_of_clearedP2_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean)
-/
@[path]
private lemma not_toggleExists_of_clearedP2_ne_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (hne : R.toPartialSelector.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ ≠ shb_segmentNum beta J d s * R.toPartialSelector.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss) :
-- imply
  ¬ R.CanonicalBondwiseToggleExists beta J d s ss hs := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.not_toggleExists_of_clearedP2_ne R beta J d s ss hs hne


-- created on 2026-10-23
