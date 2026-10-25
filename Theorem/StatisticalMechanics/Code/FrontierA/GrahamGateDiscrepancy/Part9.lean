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
import Instance.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part2


namespace StatMech.FrontierA

theorem RelationPartialMatching.exists_holeState_of_card_lt
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop)
    (hcard : Fintype.card B < Fintype.card A) :
    Nonempty (RelationPartialMatching.HoleState r) := by
  classical
  obtain ⟨matching, hmaximum⟩ := exists_maximum_relationPartialMatching r
  have hexposed : ∃ a, a ∉ matching.support := by
    by_contra hall
    push Not at hall
    have hsupport : matching.support = Finset.univ :=
      Finset.eq_univ_of_forall hall
    have hle := matching.card_support_le_target
    rw [hsupport, Finset.card_univ] at hle
    omega
  obtain ⟨a, ha⟩ := hexposed
  exact ⟨⟨matching, hmaximum, a, ha⟩⟩


end StatMech.FrontierA
