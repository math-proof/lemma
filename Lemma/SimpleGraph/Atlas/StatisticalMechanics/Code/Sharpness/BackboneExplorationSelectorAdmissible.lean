import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_cutLocalSourceSelector_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_cutLocalSourceSelector_admissible_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  {Aleft Aright : Finset V}
-- given
  (P : G.edgeFinset -> Prop)
  (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
  (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) :
-- imply
  shb_LocalSourceSelectorAdmissible G P (Aleft ∆ Aright) Aleft Aright (shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector) leftSelector rightSelector := by
-- proof
  apply StatMech.Sharpness.shb_cutLocalSourceSelector_admissible G P Aleft Aright leftSelector rightSelector

/--
[shb_cutLocalSourceSelectorMass_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_cutLocalSourceSelectorMass_factor_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred P]
  {Aleft Aright : Finset V}
  [DecidablePred leftSelector]
  [DecidablePred rightSelector]
-- given
  (J : Sym2 V -> Real)
  (P : G.edgeFinset -> Prop)
  (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
  (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) :
-- imply
  shb_cutFullPredicateMass G beta J (fun m => sources G (ofEdgeFun G m) = Aleft ∆ Aright /\ shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector m) = shb_cutLeftPredicateMass G beta J P (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\ leftSelector a) * shb_cutRightPredicateMass G beta J P (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\ rightSelector b) := by
-- proof
  apply StatMech.Sharpness.shb_cutLocalSourceSelectorMass_factor G beta J P Aleft Aright leftSelector rightSelector

/--
[shb_dynamicSegmentCutLocalSelector_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_dynamicSegmentCutLocalSelector_admissible_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {Aleft Aright : Finset V}
-- given
  (leftSelector : ({e : d.graph.edgeFinset // shb_segmentCut d.graph s e} -> Nat) -> Prop)
  (rightSelector : ({e : d.graph.edgeFinset // Not (shb_segmentCut d.graph s e)} -> Nat) -> Prop) :
-- imply
  shb_LocalSourceSelectorAdmissible d.graph (shb_segmentCut d.graph s) (Aleft ∆ Aright) Aleft Aright (shb_cutLocalSourceSelector d.graph (shb_segmentCut d.graph s) Aleft Aright leftSelector rightSelector) leftSelector rightSelector := by
-- proof
  apply StatMech.Sharpness.shb_dynamicSegmentCutLocalSelector_admissible G d s Aleft Aright leftSelector rightSelector

/--
[shb_actualExplorationFiberMass_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_actualExplorationFiberMass_eq_generated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [∀ d word, DecidablePred (selector d word)]
-- given
  (J : Sym2 V -> Real)
  (sourceClass : shb_ExplorationDomain V -> List (shb_ExplorationSegment V) -> Finset V)
  (selector : (d : shb_ExplorationDomain V) -> List (shb_ExplorationSegment V) -> (d.graph.edgeFinset -> Nat) -> Prop)
  (hrealizes : shb_ActualExplorationFiberRealizes beta J (shb_actualExplorationFiberMass beta J sourceClass selector)) :
-- imply
  shb_actualExplorationFiberMass beta J sourceClass selector = shb_generatedExplorationFiberMass beta J := by
-- proof
  apply StatMech.Sharpness.shb_actualExplorationFiberMass_eq_generated G beta J sourceClass selector hrealizes

/--
[shb_actualExplorationFiberRealizes_iff_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_actualExplorationFiberRealizes_iff_eq_generated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [∀ d word, DecidablePred (selector d word)]
-- given
  (J : Sym2 V -> Real)
  (sourceClass : shb_ExplorationDomain V -> List (shb_ExplorationSegment V) -> Finset V)
  (selector : (d : shb_ExplorationDomain V) -> List (shb_ExplorationSegment V) -> (d.graph.edgeFinset -> Nat) -> Prop) :
-- imply
  shb_ActualExplorationFiberRealizes beta J (shb_actualExplorationFiberMass beta J sourceClass selector) <-> shb_actualExplorationFiberMass beta J sourceClass selector = shb_generatedExplorationFiberMass beta J := by
-- proof
  apply StatMech.Sharpness.shb_actualExplorationFiberRealizes_iff_eq_generated G beta J sourceClass selector

/--
[shb_actualExploration_rho_eq_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_actualExploration_rho_eq_weight_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [∀ d word, DecidablePred (selector d word)]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
  (sourceClass : shb_ExplorationDomain V -> List (shb_ExplorationSegment V) -> Finset V)
  (selector : (d : shb_ExplorationDomain V) -> List (shb_ExplorationSegment V) -> (d.graph.edgeFinset -> Nat) -> Prop)
  (hrealizes : shb_ActualExplorationFiberRealizes beta J (shb_actualExplorationFiberMass beta J sourceClass selector)) :
-- imply
  shb_normalizedExplorationRho beta J (shb_actualExplorationFiberMass beta J sourceClass selector) d word = (shb_BackboneExplorationDomain.kernel beta J hbeta hJ hdom).weight d word := by
-- proof
  apply StatMech.Sharpness.shb_actualExploration_rho_eq_weight G beta J hbeta hJ hdom sourceClass selector hrealizes d word

/--
[shb_actualExploration_P2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean)
-/
@[path]
private lemma shb_actualExploration_P2_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [∀ d word, DecidablePred (selector d word)]
  {d : shb_ExplorationDomain V}
  {p q : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
  (sourceClass : shb_ExplorationDomain V -> List (shb_ExplorationSegment V) -> Finset V)
  (selector : (d : shb_ExplorationDomain V) -> List (shb_ExplorationSegment V) -> (d.graph.edgeFinset -> Nat) -> Prop)
  (hrealizes : shb_ActualExplorationFiberRealizes beta J (shb_actualExplorationFiberMass beta J sourceClass selector)) :
-- imply
  shb_normalizedExplorationRho beta J (shb_actualExplorationFiberMass beta J sourceClass selector) d (p ++ q) = shb_normalizedExplorationRho beta J (shb_actualExplorationFiberMass beta J sourceClass selector) d p * shb_normalizedExplorationRho beta J (shb_actualExplorationFiberMass beta J sourceClass selector) (shb_BackboneExplorationDomain.exploration.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_actualExploration_P2 G beta J hbeta hJ hdom sourceClass selector hrealizes d p q


-- created on 2026-10-23
