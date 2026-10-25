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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part10


namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.HoleState.move
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    RelationPartialMatching.HoleState r := by
  classical
  let old := state.occupant natural hnatural
  have hold : state.matching.toFun old = some (natural state.hole) := by
    exact state.occupant_spec natural hnatural
  let hne : state.hole ≠ old :=
    state.matching.ne_of_not_mem_support_of_eq_some
      state.hole old (natural state.hole) state.hole_unmatched hold
  let reassigned := state.matching.reassign state.hole old
    (natural state.hole) hne hold (hnatural state.hole)
  have hmaximum : reassigned.IsMaximum := by
    simpa only [reassigned] using state.maximum.reassign
      state.hole old (natural state.hole) state.hole_unmatched hold
        (hnatural state.hole)
  have holdUnmatched : old ∉ reassigned.support := by
    intro hmem
    obtain ⟨b, hb⟩ :=
      (RelationPartialMatching.mem_support_iff reassigned old).1 hmem
    have hnone : reassigned.toFun old = none := by
      simpa only [reassigned] using
        RelationPartialMatching.reassign_apply_old state.matching
          state.hole old (natural state.hole) hne hold (hnatural state.hole)
    rw [hnone] at hb
    contradiction
  exact ⟨reassigned, hmaximum, old, holdUnmatched⟩


noncomputable def RelationPartialMatching.HoleState.occupantAt
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) : A :=
  Classical.choose (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched b hincident)

end StatMech.FrontierA
