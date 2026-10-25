/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part10


namespace StatMech.FrontierA

theorem RelationPartialMatching.HoleState.matching_apply_moveAcross_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.matching.toFun (state.moveAcross b hincident).hole = some b := by
  change state.matching.toFun (state.occupantAt b hincident) = some b
  exact state.occupantAt_spec b hincident


theorem RelationPartialMatching.HoleState.moveAcross_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    (state.moveAcross b hincident).matching.toFun state.hole = some b := by
  classical
  unfold RelationPartialMatching.HoleState.moveAcross
  simp only
  apply RelationPartialMatching.reassign_apply_new


theorem RelationPartialMatching.HoleState.hole_ne_moveAcross_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.hole ≠ (state.moveAcross b hincident).hole := by
  intro h
  apply state.hole_unmatched
  apply (RelationPartialMatching.mem_support_iff state.matching state.hole).2
  exact ⟨b, h ▸ state.matching_apply_moveAcross_hole b hincident⟩


theorem RelationPartialMatching.HoleState.matching_apply_move_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    state.matching.toFun (state.move natural hnatural).hole =
      some (natural state.hole) := by
  change state.matching.toFun (state.occupant natural hnatural) =
    some (natural state.hole)
  exact state.occupant_spec natural hnatural


theorem RelationPartialMatching.HoleState.move_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    (state.move natural hnatural).matching.toFun state.hole =
      some (natural state.hole) := by
  classical
  unfold RelationPartialMatching.HoleState.move
  simp only
  apply RelationPartialMatching.reassign_apply_new


theorem RelationPartialMatching.HoleState.hole_ne_move_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    state.hole ≠ (state.move natural hnatural).hole := by
  intro h
  apply state.hole_unmatched
  apply (RelationPartialMatching.mem_support_iff
    state.matching state.hole).2
  exact ⟨natural state.hole,
    h ▸ state.matching_apply_move_hole natural hnatural⟩


theorem RelationPartialMatching.HoleState.move_matching_apply_of_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (x : A)
    (hxCurrent : x ≠ state.hole)
    (hxNext : x ≠ (state.move natural hnatural).hole) :
    (state.move natural hnatural).matching.toFun x =
      state.matching.toFun x := by
  classical
  unfold RelationPartialMatching.HoleState.move
  simp only
  apply RelationPartialMatching.reassign_apply_of_ne
  · exact hxCurrent
  · exact hxNext


end StatMech.FrontierA
