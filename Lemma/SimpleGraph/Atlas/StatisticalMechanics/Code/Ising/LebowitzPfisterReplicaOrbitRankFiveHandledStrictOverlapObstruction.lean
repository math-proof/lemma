import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part4
open StatMech StatMech.Ising StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction


/--
[flip_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_ne_eq
  {y : Target} :
-- imply
  flip y ≠ y := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.flip_ne y

/--
[flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_involutive_eq
  {y : Target} :
-- imply
  flip (flip y) = y := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.flip_involutive y

/--
[center_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma center_injective_eq :
-- imply
  Function.Injective center := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.center_injective

/--
[center_ne_flip_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma center_ne_flip_center_eq
  {a b : HandledSource} :
-- imply
  center a ≠ flip (center b) := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.center_ne_flip_center a b

/--
[candidates_card_eq_one_or_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma candidates_card_eq_one_or_two_eq
  {z : StrictSource} :
-- imply
  (candidates z).card = 1 ∨ (candidates z).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.candidates_card_eq_one_or_two z

/--
[incoming_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma incoming_classification_eq
  {y : Target} :
-- imply
  ((incomingDegree 1 y).card = 0 ∧ (incomingDegree 2 y).card ≤ 2) ∨ ((incomingDegree 1 y).card = 1 ∧ (incomingDegree 2 y).card = 0) := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.incoming_classification y

/--
[one_add_incoming_card_le_rerouteNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma one_add_incoming_card_le_rerouteNeighborhood_eq
  {y : Target} :
-- imply
  1 + (incoming y).card ≤ (rerouteNeighborhood y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.one_add_incoming_card_le_rerouteNeighborhood y

/--
[chosen_rerouteNeighborhoods_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma chosen_rerouteNeighborhoods_not_disjoint_eq :
-- imply
  ¬ Disjoint (rerouteNeighborhood (center 0)) (rerouteNeighborhood (center 1)) := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.chosen_rerouteNeighborhoods_not_disjoint

/--
[not_combined_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma not_combined_card_le_target_eq :
-- imply
  ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤ Fintype.card Target := by
-- proof
  apply StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction.not_combined_card_le_target

/--
[flip_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_ne_eq_2
  {y : Target} :
-- imply
  flip y ≠ y := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.flip_ne y

/--
[flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_involutive_eq_2
  {y : Target} :
-- imply
  flip (flip y) = y := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.flip_involutive y

/--
[every_source_degree_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma every_source_degree_one_eq
  {z : StrictSource} :
-- imply
  (candidates z).card = 1 := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.every_source_degree_one z

/--
[every_target_has_one_degree_one_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma every_target_has_one_degree_one_incoming_eq
  {y : Target} :
-- imply
  (incoming y).card = 1 := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.every_target_has_one_degree_one_incoming y

/--
[local_center_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma local_center_capacity_eq :
-- imply
  1 + (incoming (center ())).card ≤ (component (center ())).card := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.local_center_capacity

/--
[mate_closed_component_has_no_extra_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma mate_closed_component_has_no_extra_capacity_eq :
-- imply
  (pairIncoming (center ())).card = (component (center ())).card ∧ ¬ 1 + (pairIncoming (center ())).card ≤ (component (center ())).card := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.mate_closed_component_has_no_extra_capacity

/--
[not_combined_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma not_combined_card_le_target_eq_2 :
-- imply
  ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤ Fintype.card Target := by
-- proof
  apply StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction.not_combined_card_le_target

/--
[flip_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_ne_eq_3
  {y : Target} :
-- imply
  flip y ≠ y := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.flip_ne y

/--
[flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_involutive_eq_3
  {y : Target} :
-- imply
  flip (flip y) = y := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.flip_involutive y

/--
[every_source_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma every_source_degree_two_eq
  {z : StrictSource} :
-- imply
  (candidates z).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.every_source_degree_two z

/--
[both_mates_have_no_degree_one_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma both_mates_have_no_degree_one_incoming_eq
  {y : Target} :
-- imply
  (incomingDegree 1 y).card = 0 ∧ (incomingDegree 1 (flip y)).card = 0 := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.both_mates_have_no_degree_one_incoming y

/--
[incoming_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma incoming_classification_eq_2
  {y : Target} :
-- imply
  (incomingDegree 1 y).card = 0 ∧ (incomingDegree 2 y).card ≤ 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.incoming_classification y

/--
[strict_component_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma strict_component_saturated_eq
  {y : Target} :
-- imply
  Fintype.card StrictSource = (component y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.strict_component_saturated y

/--
[no_component_slack_for_handled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma no_component_slack_for_handled_eq
  {y : Target} :
-- imply
  ¬ 1 + Fintype.card StrictSource ≤ (component y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.no_component_slack_for_handled y

/--
[not_combined_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma not_combined_card_le_target_eq_3 :
-- imply
  ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤ Fintype.card Target := by
-- proof
  apply StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction.not_combined_card_le_target

/--
[flip_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_ne_eq_4
  {y : Target} :
-- imply
  flip y ≠ y := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.flip_ne y

/--
[flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma flip_involutive_eq_4
  {y : Target} :
-- imply
  flip (flip y) = y := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.flip_involutive y

/--
[every_source_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma every_source_degree_two_eq_2
  {z : StrictSource} :
-- imply
  (candidates z).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.every_source_degree_two z

/--
[every_target_has_two_degree_two_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma every_target_has_two_degree_two_incoming_eq
  {y : Target} :
-- imply
  (incomingDegree 1 y).card = 0 ∧ (incomingDegree 2 y).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.every_target_has_two_degree_two_incoming y

/--
[exists_alternate_ne_target_ne_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma exists_alternate_ne_target_ne_flip_eq
  {z : StrictSource}
  {y : Target}
-- given
  (hzy : Related z y) :
-- imply
  ∃ y', Related z y' ∧ y' ≠ y ∧ y' ≠ flip y := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.exists_alternate_ne_target_ne_flip z y hzy

/--
[one_add_incoming_card_le_rerouteNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma one_add_incoming_card_le_rerouteNeighborhood_eq_2
  {y : Target} :
-- imply
  1 + (incoming y).card ≤ (rerouteNeighborhood y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.one_add_incoming_card_le_rerouteNeighborhood y

/--
[strict_component_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma strict_component_saturated_eq_2
  {y : Target} :
-- imply
  Fintype.card StrictSource = (component y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.strict_component_saturated y

/--
[no_component_slack_for_handled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma no_component_slack_for_handled_eq_2
  {y : Target} :
-- imply
  ¬ 1 + Fintype.card StrictSource ≤ (component y).card := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.no_component_slack_for_handled y

/--
[not_combined_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean)
-/
@[path]
private lemma not_combined_card_le_target_eq_4 :
-- imply
  ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤ Fintype.card Target := by
-- proof
  apply StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction.not_combined_card_le_target


-- created on 2026-10-23
