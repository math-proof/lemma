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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part11


namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.HoleState.moveAcross
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    RelationPartialMatching.HoleState r := by
  classical
  let old := state.occupantAt b hincident
  have hold : state.matching.toFun old = some b :=
    state.occupantAt_spec b hincident
  let hne : state.hole ≠ old :=
    state.matching.ne_of_not_mem_support_of_eq_some
      state.hole old b state.hole_unmatched hold
  let reassigned := state.matching.reassign state.hole old b hne hold hincident
  have hmaximum : reassigned.IsMaximum := by
    simpa only [reassigned] using state.maximum.reassign
      state.hole old b state.hole_unmatched hold hincident
  have holdUnmatched : old ∉ reassigned.support := by
    intro hmem
    obtain ⟨target, htarget⟩ :=
      (RelationPartialMatching.mem_support_iff reassigned old).1 hmem
    have hnone : reassigned.toFun old = none := by
      simpa only [reassigned] using
        RelationPartialMatching.reassign_apply_old state.matching
          state.hole old b hne hold hincident
    rw [hnone] at htarget
    contradiction
  exact ⟨reassigned, hmaximum, old, holdUnmatched⟩


end StatMech.FrontierA
