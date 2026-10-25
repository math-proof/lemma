/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part9


namespace StatMech.Onsager

open BigOperators Finset

@[simp] theorem ons_decRootedAtomEquivRootedList_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecRootedAtom L d) :
    (ons_decRootedAtomEquivRootedList L d atom).1 =
      ons_decRootedAtomList atom := rfl

theorem ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton
    {E : Type*} [DecidableEq E] (e r : E)
    (w : List E) (hw : ons_validRootedList e r w) :
    ons_firstReturnFactors e w = [] ↔ w = [e] := by
  constructor
  · intro hfactors
    have hspec := ons_firstReturnFactors_spec e w hw.1 hw.2.1
    rw [← hspec.2.2, hfactors]
    rfl
  · rintro rfl
    simp [ons_firstReturnFactors, ons_firstReturnSplit]

theorem ons_rootedList_nontrivial_iff_factors_ne_nil
    {E : Type*} [DecidableEq E] (e r : E)
    (w : List E) (hw : ons_validRootedList e r w) :
    2 ≤ w.length ↔ ons_firstReturnFactors e w ≠ [] := by
  rw [ne_eq, ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton e r w hw]
  constructor
  · intro hlength hwone
    rw [hwone] at hlength
    simp at hlength
  · intro hwone
    have hpos : 0 < w.length := by
      apply List.length_pos_iff.mpr
      intro hwempty
      have hhead := hw.1
      rw [hwempty] at hhead
      simp at hhead
    by_contra hlength
    have hone : w.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
    apply hwone
    rw [hx] at hw ⊢
    simpa using hw.1


end StatMech.Onsager
