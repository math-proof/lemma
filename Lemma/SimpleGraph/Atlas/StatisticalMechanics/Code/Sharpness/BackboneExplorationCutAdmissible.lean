import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_summable_cutLeftPredicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_summable_cutLeftPredicate_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred P]
  [DecidablePred left]
-- given
  (J : Sym2 V -> Real)
  (P : G.edgeFinset -> Prop)
  (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop) :
-- imply
  Summable (fun a => if left a then shb_cutLeftWeight G beta J P a else 0) := by
-- proof
  apply StatMech.Sharpness.shb_summable_cutLeftPredicate G beta J P left

/--
[shb_summable_cutRightPredicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_summable_cutRightPredicate_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred P]
  [DecidablePred right]
-- given
  (J : Sym2 V -> Real)
  (P : G.edgeFinset -> Prop)
  (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) :
-- imply
  Summable (fun b => if right b then shb_cutRightWeight G beta J P b else 0) := by
-- proof
  apply StatMech.Sharpness.shb_summable_cutRightPredicate G beta J P right

/--
[shb_cutPredicateMass_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_cutPredicateMass_factor_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred P]
  [DecidablePred full]
  [DecidablePred left]
  [DecidablePred right]
-- given
  (J : Sym2 V -> Real)
  (P : G.edgeFinset -> Prop)
  (full : (G.edgeFinset -> Nat) -> Prop)
  (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
  (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
  (hadm : shb_CutPredicateAdmissible G P full left right) :
-- imply
  shb_cutFullPredicateMass G beta J full = shb_cutLeftPredicateMass G beta J P left * shb_cutRightPredicateMass G beta J P right := by
-- proof
  apply StatMech.Sharpness.shb_cutPredicateMass_factor G beta J P full left right hadm

/--
[shb_sources_cutJoin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_sources_cutJoin_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  (a b)
-- given
  (P : G.edgeFinset -> Prop) :
-- imply
  sources G (ofEdgeFun G (shb_cutJoin G P (a, b))) = sources G (ofEdgeFun G (shb_cutLeft G P a)) ∆ sources G (ofEdgeFun G (shb_cutRight G P b)) := by
-- proof
  apply StatMech.Sharpness.shb_sources_cutJoin G P

/--
[shb_localSourceSelectorMass_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_localSourceSelectorMass_factor_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred P]
  {A Aleft Aright : Finset V}
  [DecidablePred selector]
  [DecidablePred leftSelector]
  [DecidablePred rightSelector]
-- given
  (J : Sym2 V -> Real)
  (P : G.edgeFinset -> Prop)
  (selector : (G.edgeFinset -> Nat) -> Prop)
  (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
  (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
  (hadm : shb_LocalSourceSelectorAdmissible G P A Aleft Aright selector leftSelector rightSelector) :
-- imply
  shb_cutFullPredicateMass G beta J (fun m => sources G (ofEdgeFun G m) = A /\ selector m) = shb_cutLeftPredicateMass G beta J P (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\ leftSelector a) * shb_cutRightPredicateMass G beta J P (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\ rightSelector b) := by
-- proof
  apply StatMech.Sharpness.shb_localSourceSelectorMass_factor G beta J P A Aleft Aright selector leftSelector rightSelector hadm

/--
[shb_generatedExplorationFiberMass_cutResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_generatedExplorationFiberMass_cutResummation_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_LocalSelectorFiberCutResummation beta J (shb_generatedExplorationFiberMass beta J : shb_ExplorationFiberMass V) := by
-- proof
  apply StatMech.Sharpness.shb_generatedExplorationFiberMass_cutResummation G beta J

/--
[shb_LocalSelectorFiberCutResummation_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_LocalSelectorFiberCutResummation_unique_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {fiberMass : shb_ExplorationFiberMass V}
-- given
  (J : Sym2 V -> Real)
  (hcut : shb_LocalSelectorFiberCutResummation beta J fiberMass) :
-- imply
  fiberMass = shb_generatedExplorationFiberMass beta J := by
-- proof
  apply StatMech.Sharpness.shb_LocalSelectorFiberCutResummation_unique G beta J fiberMass hcut

/--
[shb_LocalSelectorFiberCutResummation_iff_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean)
-/
@[path]
private lemma shb_LocalSelectorFiberCutResummation_iff_eq_generated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {fiberMass : shb_ExplorationFiberMass V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_LocalSelectorFiberCutResummation beta J fiberMass <-> fiberMass = shb_generatedExplorationFiberMass beta J := by
-- proof
  apply StatMech.Sharpness.shb_LocalSelectorFiberCutResummation_iff_eq_generated G beta J fiberMass


-- created on 2026-10-23
