import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneConcreteSelector


/--
[exists_labeled_split_of_rawSourcePairFiberMass_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelectorObstruction.lean)
-/
@[path]
private lemma exists_labeled_split_of_rawSourcePairFiberMass_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  [DecidablePred Q]
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (Q R : (G.edgeFinset -> Nat) -> Prop)
  (hmass : rawSourcePairFiberMass G beta J m A Q R ≠ 0) :
-- imply
  ∃ T : Finset (Copy G m), RandomCurrent.sources (endsM G m) T = A /\ Q (profileFlux G m T) /\ R (profileFlux G m (univ \ T)) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.exists_labeled_split_of_rawSourcePairFiberMass_ne_zero G beta J m A Q R hmass

/--
[BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelectorObstruction.lean)
-/
@[path]
private lemma stepToggleSource_eq_empty_of_contributes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix1 suffix2 : List (Sym2 V)}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs}
-- given
  (bit1 bit2 : Nat -> Bool)
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes S beta J d s ss hs m) :
-- imply
  stepToggleSource S d s ss = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs C m hm

/--
[BondwiseCoordinateCertificate.not_contributes_of_toggleSource_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelectorObstruction.lean)
-/
@[path]
private lemma not_contributes_of_toggleSource_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix1 suffix2 : List (Sym2 V)}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs}
-- given
  (bit1 bit2 : Nat -> Bool)
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (hsource : stepToggleSource S d s ss ≠ ∅)
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  ¬ CoordinatePairContributes S beta J d s ss hs m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.BondwiseCoordinateCertificate.not_contributes_of_toggleSource_ne_empty X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs C hsource m

/--
[bondwiseCoordinateCertificate_isEmpty_of_contributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelectorObstruction.lean)
-/
@[path]
private lemma bondwiseCoordinateCertificate_isEmpty_of_contributes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix1 suffix2 : List (Sym2 V)}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (bit1 bit2 : Nat -> Bool)
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (m : d.graph.edgeFinset -> Nat)
  (hm : CoordinatePairContributes S beta J d s ss hs m)
  (hsource : stepToggleSource S d s ss ≠ ∅) :
-- imply
  IsEmpty (BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.bondwiseCoordinateCertificate_isEmpty_of_contributes X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs m hm hsource

/--
[bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelectorObstruction.lean)
-/
@[path]
private lemma bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix1 suffix2 : List (Sym2 V)}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (bit1 bit2 : Nat -> Bool)
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (hmass : S.actualMass beta J d (s :: ss) ≠ 0)
  (hsource : stepToggleSource S d s ss ≠ ∅) :
-- imply
  IsEmpty (BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs hmass hsource


-- created on 2026-10-23
