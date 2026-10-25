import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
open Finset


/--
[finiteRelationHall_of_fractionalWeights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FractionalHall.lean)
-/
@[path]
private lemma finiteRelationHall_of_fractionalWeights_eq
  [Fintype Source]
  [Fintype Target]
  [DecidableRel related]
-- given
  (related : Source -> Target -> Prop)
  (weight : Source -> Target -> Real)
  (hnonneg : forall source target, 0 <= weight source target)
  (hsupport : forall source target, Not (related source target) -> weight source target = 0)
  (hsource : forall source, 1 <= ∑ target, weight source target)
  (htarget : forall target, ∑ source, weight source target <= 1) :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target => ∃ source ∈ sources, related source target).card := by
-- proof
  apply finiteRelationHall_of_fractionalWeights related weight hnonneg hsupport hsource htarget

/--
[finiteSubset_card_lt_of_fractionalWeights_of_target_slack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FractionalHall.lean)
-/
@[path]
private lemma finiteSubset_card_lt_of_fractionalWeights_of_target_slack_eq
  {sources : Finset Source}
  {targets : Finset Target}
  {slackTarget : Target}
-- given
  (weight : Source -> Target -> Real)
  (hsource : forall source, source ∈ sources -> (∑ target ∈ targets, weight source target) = 1)
  (htarget : forall target, target ∈ targets -> (∑ source ∈ sources, weight source target) ≤ 1)
  (hslackMem : slackTarget ∈ targets)
  (hslack : (∑ source ∈ sources, weight source slackTarget) < 1) :
-- imply
  sources.card < targets.card := by
-- proof
  apply finiteSubset_card_lt_of_fractionalWeights_of_target_slack weight sources targets hsource htarget slackTarget hslackMem hslack


-- created on 2026-10-23
