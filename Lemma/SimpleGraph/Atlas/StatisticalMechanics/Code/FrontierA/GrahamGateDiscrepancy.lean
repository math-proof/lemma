import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
open StatMech StatMech.FrontierA


/--
[card_subtype_le_iff_card_leftOnly_le_card_rightOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_subtype_le_iff_card_leftOnly_le_card_rightOnly_eq
  [Fintype A]
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (P Q : A -> Prop) :
-- imply
  Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} ↔ Fintype.card {a : A // P a ∧ ¬ Q a} <= Fintype.card {a : A // ¬ P a ∧ Q a} := by
-- proof
  apply StatMech.FrontierA.card_subtype_le_iff_card_leftOnly_le_card_rightOnly P Q

/--
[card_subtype_le_of_discrepancyEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_subtype_le_of_discrepancyEmbedding_eq
  [Fintype A]
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (P Q : A -> Prop)
  (f : {a : A // P a ∧ ¬ Q a} ↪ {a : A // ¬ P a ∧ Q a}) :
-- imply
  Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
-- proof
  apply StatMech.FrontierA.card_subtype_le_of_discrepancyEmbedding P Q f

/--
[mem_functionWeakComponent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma mem_functionWeakComponent_self_eq
  {x : B}
-- given
  (next : B -> B) :
-- imply
  x ∈ functionWeakComponent next x := by
-- proof
  apply StatMech.FrontierA.mem_functionWeakComponent_self next x

/--
[functionWeakComponent_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma functionWeakComponent_eq_of_mem_eq
  {x y : B}
-- given
  (next : B -> B)
  (hxy : y ∈ functionWeakComponent next x) :
-- imply
  functionWeakComponent next x = functionWeakComponent next y := by
-- proof
  apply StatMech.FrontierA.functionWeakComponent_eq_of_mem next hxy

/--
[functionWeakComponent_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma functionWeakComponent_next_eq
  {x : B}
-- given
  (next : B -> B) :
-- imply
  functionWeakComponent next (next x) = functionWeakComponent next x := by
-- proof
  apply StatMech.FrontierA.functionWeakComponent_next next x

/--
[crossCollision_fst_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma crossCollision_fst_injective_eq
  {f : A ↪ C}
  {g : B ↪ C} :
-- imply
  Function.Injective fun collision : crossCollision f g => collision.1.1 := by
-- proof
  apply StatMech.FrontierA.crossCollision_fst_injective f g

/--
[crossCollision_snd_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma crossCollision_snd_injective_eq
  {f : A ↪ C}
  {g : B ↪ C} :
-- imply
  Function.Injective fun collision : crossCollision f g => collision.1.2 := by
-- proof
  apply StatMech.FrontierA.crossCollision_snd_injective f g

/--
[exists_secondCollisionCharge_of_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_secondCollisionCharge_of_card_le_eq
  [Fintype A]
  [Fintype B]
  [Fintype C]
  {f : A ↪ C}
  {g : B ↪ C}
  {first : crossCollision f g ↪ C}
-- given
  (hfirstFreshLeft : ∀ collision a, first collision ≠ f a)
  (hcard : Fintype.card A + Fintype.card B ≤ Fintype.card C) :
-- imply
  ∃ second : crossCollision first g ↪ C, (∀ collision a, second collision ≠ f a) ∧ (∀ collision b, second collision ≠ g b) ∧ ∀ collision old, second collision ≠ first old := by
-- proof
  apply StatMech.FrontierA.exists_secondCollisionCharge_of_card_le f g first hfirstFreshLeft hcard

/--
[RelationPartialMatching.mem_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma mem_support_iff_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {a : A} :
-- imply
  a ∈ matching.support ↔ ∃ b, matching.toFun a = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.mem_support_iff matching a

/--
[exists_maximum_relationPartialMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_maximum_relationPartialMatching_eq
  [Fintype A]
  [Fintype B]
-- given
  (r : A -> B -> Prop) :
-- imply
  ∃ matching : RelationPartialMatching r, matching.IsMaximum := by
-- proof
  apply StatMech.FrontierA.exists_maximum_relationPartialMatching r

/--
[exists_relationPartialMatching_saturating_unmatched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_relationPartialMatching_saturating_unmatched_eq
  [Fintype A]
  [Fintype B]
-- given
  (r : A -> B -> Prop) :
-- imply
  ∃ matching : RelationPartialMatching r, matching.IsMaximum ∧ ∀ a, a ∉ matching.support -> ∀ b, r a b -> ∃ a', matching.toFun a' = some b := by
-- proof
  apply StatMech.FrontierA.exists_relationPartialMatching_saturating_unmatched r

/--
[RelationPartialMatching.reassign_apply_new](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma reassign_apply_new_eq
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hne : new ≠ old)
  (hold : matching.toFun old = some b)
  (hnew : r new b) :
-- imply
  (matching.reassign new old b hne hold hnew).toFun new = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.reassign_apply_new matching new old b hne hold hnew

/--
[RelationPartialMatching.reassign_apply_old](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma reassign_apply_old_eq
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hne : new ≠ old)
  (hold : matching.toFun old = some b)
  (hnew : r new b) :
-- imply
  (matching.reassign new old b hne hold hnew).toFun old = none := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.reassign_apply_old matching new old b hne hold hnew

/--
[RelationPartialMatching.reassign_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma reassign_apply_of_ne_eq
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old x : A}
  {b : B}
-- given
  (hne : new ≠ old)
  (hold : matching.toFun old = some b)
  (hnew : r new b)
  (hxNew : x ≠ new)
  (hxOld : x ≠ old) :
-- imply
  (matching.reassign new old b hne hold hnew).toFun x = matching.toFun x := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.reassign_apply_of_ne matching new old x b hne hold hnew hxNew hxOld

/--
[RelationPartialMatching.support_reassign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma support_reassign_eq
  [Fintype A]
  [DecidableEq A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hne : new ≠ old)
  (hold : matching.toFun old = some b)
  (hnew : r new b) :
-- imply
  (matching.reassign new old b hne hold hnew).support = insert new (matching.support.erase old) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.support_reassign matching new old b hne hold hnew

/--
[RelationPartialMatching.ne_of_not_mem_support_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma ne_of_not_mem_support_of_eq_some_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hnewUnmatched : new ∉ matching.support)
  (hold : matching.toFun old = some b) :
-- imply
  new ≠ old := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.ne_of_not_mem_support_of_eq_some matching new old b hnewUnmatched hold

/--
[RelationPartialMatching.card_support_reassign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_support_reassign_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hnewUnmatched : new ∉ matching.support)
  (hold : matching.toFun old = some b)
  (hnew : r new b) :
-- imply
  (matching.reassign new old b (matching.ne_of_not_mem_support_of_eq_some new old b hnewUnmatched hold) hold hnew).support.card = matching.support.card := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.card_support_reassign matching new old b hnewUnmatched hold hnew

/--
[RelationPartialMatching.IsMaximum.reassign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma reassign_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {new old : A}
  {b : B}
-- given
  (hmaximum : matching.IsMaximum)
  (hnewUnmatched : new ∉ matching.support)
  (hold : matching.toFun old = some b)
  (hnew : r new b) :
-- imply
  (matching.reassign new old b (matching.ne_of_not_mem_support_of_eq_some new old b hnewUnmatched hold) hold hnew).IsMaximum := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.IsMaximum.reassign hmaximum new old b hnewUnmatched hold hnew

/--
[RelationPartialMatching.IsMaximum.saturates_target_of_unmatched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma saturates_target_of_unmatched_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {a : A}
  {b : B}
-- given
  (hmaximum : matching.IsMaximum)
  (ha : a ∉ matching.support)
  (hab : r a b) :
-- imply
  ∃ a', matching.toFun a' = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.IsMaximum.saturates_target_of_unmatched hmaximum a ha b hab

/--
[RelationPartialMatching.card_support_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_support_le_target_eq
  [Fintype A]
  [Fintype B]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r} :
-- imply
  matching.support.card ≤ Fintype.card B := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.card_support_le_target matching

/--
[RelationPartialMatching.saturates_all_targets_of_card_support_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma saturates_all_targets_of_card_support_eq_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {b : B}
-- given
  (hcard : matching.support.card = Fintype.card B) :
-- imply
  ∃ a, matching.toFun a = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.saturates_all_targets_of_card_support_eq matching hcard b

/--
[RelationPartialMatching.targetPreimage_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma targetPreimage_spec_eq
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
  {b : B}
-- given
  (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) :
-- imply
  matching.toFun (matching.targetPreimage hsaturated b) = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.targetPreimage_spec matching hsaturated b

/--
[RelationPartialMatching.targetPreimage_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma targetPreimage_injective_eq
  {r : A -> B -> Prop}
  {matching : RelationPartialMatching r}
-- given
  (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) :
-- imply
  Function.Injective (matching.targetPreimage hsaturated) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.targetPreimage_injective matching hsaturated

/--
[RelationPartialMatching.exists_holeState_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_holeState_of_card_lt_eq
  [Fintype A]
  [Fintype B]
-- given
  (r : A -> B -> Prop)
  (hcard : Fintype.card B < Fintype.card A) :
-- imply
  Nonempty (RelationPartialMatching.HoleState r) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.exists_holeState_of_card_lt r hcard

/--
[RelationPartialMatching.HoleState.occupant_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma occupant_spec_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  state.matching.toFun (state.occupant natural hnatural) = some (natural state.hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.occupant_spec natural hnatural state

/--
[RelationPartialMatching.HoleState.occupantAt_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma occupantAt_spec_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {b : B}
-- given
  (hincident : r state.hole b) :
-- imply
  state.matching.toFun (state.occupantAt b hincident) = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.occupantAt_spec state b hincident

/--
[RelationPartialMatching.HoleState.matching_apply_moveAcross_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma matching_apply_moveAcross_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {b : B}
-- given
  (hincident : r state.hole b) :
-- imply
  state.matching.toFun (state.moveAcross b hincident).hole = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.matching_apply_moveAcross_hole state b hincident

/--
[RelationPartialMatching.HoleState.moveAcross_matching_apply_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma moveAcross_matching_apply_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {b : B}
-- given
  (hincident : r state.hole b) :
-- imply
  (state.moveAcross b hincident).matching.toFun state.hole = some b := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.moveAcross_matching_apply_hole state b hincident

/--
[RelationPartialMatching.HoleState.hole_ne_moveAcross_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma hole_ne_moveAcross_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {b : B}
-- given
  (hincident : r state.hole b) :
-- imply
  state.hole ≠ (state.moveAcross b hincident).hole := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.hole_ne_moveAcross_hole state b hincident

/--
[RelationPartialMatching.HoleState.matching_apply_move_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma matching_apply_move_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  state.matching.toFun (state.move natural hnatural).hole = some (natural state.hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.matching_apply_move_hole natural hnatural state

/--
[RelationPartialMatching.HoleState.move_matching_apply_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma move_matching_apply_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  (state.move natural hnatural).matching.toFun state.hole = some (natural state.hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.move_matching_apply_hole natural hnatural state

/--
[RelationPartialMatching.HoleState.hole_ne_move_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma hole_ne_move_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  state.hole ≠ (state.move natural hnatural).hole := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.hole_ne_move_hole natural hnatural state

/--
[RelationPartialMatching.HoleState.move_matching_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma move_matching_apply_of_ne_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {x : A}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hxCurrent : x ≠ state.hole)
  (hxNext : x ≠ (state.move natural hnatural).hole) :
-- imply
  (state.move natural hnatural).matching.toFun x = state.matching.toFun x := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.move_matching_apply_of_ne natural hnatural state x hxCurrent hxNext

/--
[RelationPartialMatching.HoleState.card_naturalSupport_lt_move_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_naturalSupport_lt_move_of_ne_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hne : natural state.hole ≠ natural (state.move natural hnatural).hole) :
-- imply
  (state.naturalSupport natural).card < ((state.move natural hnatural).naturalSupport natural).card := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.card_naturalSupport_lt_move_of_ne natural hnatural state hne

/--
[RelationPartialMatching.exists_maximalNatural_holeState_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_maximalNatural_holeState_collision_eq
  [Fintype A]
  [Fintype B]
-- given
  (r : A -> B -> Prop)
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hcard : Fintype.card B < Fintype.card A) :
-- imply
  ∃ state : RelationPartialMatching.HoleState r, state.hole ≠ (state.move natural hnatural).hole ∧ natural state.hole = natural (state.move natural hnatural).hole := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision r natural hnatural hcard

/--
[RelationPartialMatching.HoleState.move_move_hole_eq_of_natural_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma move_move_hole_eq_of_natural_eq_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (heq : natural state.hole = natural (state.move natural hnatural).hole) :
-- imply
  ((state.move natural hnatural).move natural hnatural).hole = state.hole := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.move_move_hole_eq_of_natural_eq natural hnatural state heq

/--
[RelationPartialMatching.HoleState.iterate_matching_apply_next_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma iterate_matching_apply_next_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {n : Nat}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  let move := RelationPartialMatching.HoleState.move natural hnatural (move^[n] state).matching.toFun (move^[n + 1] state).hole = some (natural (move^[n] state).hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.iterate_matching_apply_next_hole natural hnatural state n

/--
[RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma iterate_succ_matching_apply_hole_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {n : Nat}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  let move := RelationPartialMatching.HoleState.move natural hnatural (move^[n + 1] state).matching.toFun (move^[n] state).hole = some (natural (move^[n] state).hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole natural hnatural state n

/--
[RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma iterate_matching_apply_eq_of_avoids_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {start stop : Nat}
  {x : A}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hstartStop : start ≤ stop)
  (havoids : ∀ n : Nat, start ≤ n -> n < stop -> x ≠ ((RelationPartialMatching.HoleState.move natural hnatural)^[n] state).hole ∧ x ≠ ((RelationPartialMatching.HoleState.move natural hnatural)^[n + 1] state).hole) :
-- imply
  ((RelationPartialMatching.HoleState.move natural hnatural)^[stop] state).matching.toFun x = ((RelationPartialMatching.HoleState.move natural hnatural)^[start] state).matching.toFun x := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids natural hnatural state start stop hstartStop x havoids

/--
[RelationPartialMatching.HoleState.first_repeat_interior_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma first_repeat_interior_matching_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {start stop : Nat}
  {q : Nat}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hstartStop : start < stop)
  (hrepeat : ((RelationPartialMatching.HoleState.move natural hnatural)^[start] state).hole = ((RelationPartialMatching.HoleState.move natural hnatural)^[stop] state).hole)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((RelationPartialMatching.HoleState.move natural hnatural)^[a] state).hole ≠ ((RelationPartialMatching.HoleState.move natural hnatural)^[b] state).hole)
  (hqStart : start < q)
  (hqStop : q < stop) :
-- imply
  ((RelationPartialMatching.HoleState.move natural hnatural)^[stop] state).matching.toFun (((RelationPartialMatching.HoleState.move natural hnatural)^[q] state).hole) = some (natural (((RelationPartialMatching.HoleState.move natural hnatural)^[q] state).hole)) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.first_repeat_interior_matching natural hnatural state start stop hstartStop hrepeat hdistinct q hqStart hqStop

/--
[RelationPartialMatching.HoleState.first_repeat_interior_natural_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma first_repeat_interior_natural_ne_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
  {start stop : Nat}
  {q u : Nat}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a))
  (hstartStop : start < stop)
  (hrepeat : ((RelationPartialMatching.HoleState.move natural hnatural)^[start] state).hole = ((RelationPartialMatching.HoleState.move natural hnatural)^[stop] state).hole)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((RelationPartialMatching.HoleState.move natural hnatural)^[a] state).hole ≠ ((RelationPartialMatching.HoleState.move natural hnatural)^[b] state).hole)
  (hqStart : start < q)
  (hqStop : q < stop)
  (huStart : start < u)
  (huStop : u < stop)
  (hqu : q ≠ u) :
-- imply
  natural (((RelationPartialMatching.HoleState.move natural hnatural)^[q] state).hole) ≠ natural (((RelationPartialMatching.HoleState.move natural hnatural)^[u] state).hole) := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.first_repeat_interior_natural_ne natural hnatural state start stop hstartStop hrepeat hdistinct q u hqStart hqStop huStart huStop hqu

/--
[RelationPartialMatching.HoleState.exists_minimal_hole_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_minimal_hole_repeat_eq
  [Fintype A]
  {r : A -> B -> Prop}
  {state : RelationPartialMatching.HoleState r}
-- given
  (natural : A -> B)
  (hnatural : ∀ a, r a (natural a)) :
-- imply
  let move := RelationPartialMatching.HoleState.move natural hnatural ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card A ∧ (move^[start] state).hole = (move^[stop] state).hole ∧ ∀ a b : Nat, a < b -> b < stop -> (move^[a] state).hole ≠ (move^[b] state).hole := by
-- proof
  apply StatMech.FrontierA.RelationPartialMatching.HoleState.exists_minimal_hole_repeat natural hnatural state

/--
[card_subtype_le_of_tag_preserving_fiberwise_discrepancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_subtype_le_of_tag_preserving_fiberwise_discrepancy_eq
  [Fintype A]
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (P Q : A -> Prop)
  (sourceTag : {a : A // P a ∧ ¬ Q a} -> S)
  (targetTag : {a : A // ¬ P a ∧ Q a} -> S)
  (f : {a : A // P a ∧ ¬ Q a} -> {a : A // ¬ P a ∧ Q a})
  (htag : ∀ x, targetTag (f x) = sourceTag x)
  (hfiber : ∀ s, Function.Injective fun x : {x : {a : A // P a ∧ ¬ Q a} // sourceTag x = s} => f x.1) :
-- imply
  Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
-- proof
  apply StatMech.FrontierA.card_subtype_le_of_tag_preserving_fiberwise_discrepancy P Q sourceTag targetTag f htag hfiber

/--
[mem_finiteCommonClosureStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma mem_finiteCommonClosureStep_eq
  [Fintype A]
  {S : Finset A}
  {x : A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  x ∈ finiteCommonClosureStep P Q R S ↔ x ∈ S ∨ (x ∈ finiteRelationNeighborhood R S ∧ P x ∧ Q x) := by
-- proof
  apply StatMech.FrontierA.mem_finiteCommonClosureStep P Q R S x

/--
[subset_finiteCommonClosureStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma subset_finiteCommonClosureStep_eq
  [Fintype A]
  {S : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  S ⊆ finiteCommonClosureStep P Q R S := by
-- proof
  apply StatMech.FrontierA.subset_finiteCommonClosureStep P Q R S

/--
[finiteRelationNeighborhood_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteRelationNeighborhood_mono_eq
  [Fintype A]
  {S T : Finset A}
-- given
  (R : A -> A -> Prop)
  (hST : S ⊆ T) :
-- imply
  finiteRelationNeighborhood R S ⊆ finiteRelationNeighborhood R T := by
-- proof
  apply StatMech.FrontierA.finiteRelationNeighborhood_mono R hST

/--
[finiteCommonClosureStep_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureStep_mono_eq
  [Fintype A]
  {S T : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop)
  (hST : S ⊆ T) :
-- imply
  finiteCommonClosureStep P Q R S ⊆ finiteCommonClosureStep P Q R T := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureStep_mono P Q R hST

/--
[finiteCommonClosureIter_subset_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureIter_subset_succ_eq
  [Fintype A]
  {S : Finset A}
  {n : Nat}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  finiteCommonClosureIter P Q R S n ⊆ finiteCommonClosureIter P Q R S (n + 1) := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureIter_subset_succ P Q R S n

/--
[finiteCommonClosureIter_zero_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureIter_zero_subset_eq
  [Fintype A]
  {S : Finset A}
  {n : Nat}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  S ⊆ finiteCommonClosureIter P Q R S n := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureIter_zero_subset P Q R S n

/--
[finiteCommonClosureIter_preserves_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureIter_preserves_left_eq
  [Fintype A]
  {S : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop)
  (hS : ∀ x ∈ S, P x) :
-- imply
  ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> P x := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureIter_preserves_left P Q R S hS

/--
[finiteCommonClosureIter_common_mem_neighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureIter_common_mem_neighborhood_eq
  [Fintype A]
  {S : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop)
  (hS : ∀ x ∈ S, ¬ Q x) :
-- imply
  ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> Q x -> x ∈ finiteRelationNeighborhood R (finiteCommonClosureIter P Q R S n) := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureIter_common_mem_neighborhood P Q R S hS

/--
[finiteCommonClosureIter_succ_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma finiteCommonClosureIter_succ_start_eq
  [Fintype A]
  {S : Finset A}
  {n : Nat}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  finiteCommonClosureIter P Q R S (n + 1) = finiteCommonClosureIter P Q R (finiteCommonClosureStep P Q R S) n := by
-- proof
  apply StatMech.FrontierA.finiteCommonClosureIter_succ_start P Q R S n

/--
[exists_finiteCommonClosureIter_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma exists_finiteCommonClosureIter_fixed_eq
  [Fintype A]
  {S : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop) :
-- imply
  ∃ n ≤ Fintype.card A - S.card, finiteCommonClosureIter P Q R S (n + 1) = finiteCommonClosureIter P Q R S n := by
-- proof
  apply StatMech.FrontierA.exists_finiteCommonClosureIter_fixed P Q R S

/--
[card_leftOnly_le_rightOnly_of_commonClosed_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean)
-/
@[path]
private lemma card_leftOnly_le_rightOnly_of_commonClosed_expansion_eq
  [Fintype A]
  [DecidablePred P]
  [DecidablePred Q]
  {T : Finset A}
-- given
  (P Q : A -> Prop)
  (R : A -> A -> Prop)
  (hrel : ∀ {x y}, R x y -> P x ∧ Q y)
  (hnegative : Finset.univ.filter (fun x => P x ∧ ¬ Q x) ⊆ T)
  (hleft : ∀ x ∈ T, P x)
  (hclosed : finiteCommonClosureStep P Q R T = T)
  (hexpand : T.card ≤ (finiteRelationNeighborhood R T).card) :
-- imply
  (Finset.univ.filter fun x => P x ∧ ¬ Q x).card ≤ (Finset.univ.filter fun x => ¬ P x ∧ Q x).card := by
-- proof
  apply StatMech.FrontierA.card_leftOnly_le_rightOnly_of_commonClosed_expansion P Q R T hrel hnegative hleft hclosed hexpand


-- created on 2026-10-23
