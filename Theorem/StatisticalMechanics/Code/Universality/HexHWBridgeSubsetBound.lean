/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12


namespace StatMech.Universality

open scoped BigOperators


theorem strictDecreasingWidths_eq_of_mem_iff
    {xs ys : List HexBridge}
    (hx : StrictDecreasingWidths xs) (hy : StrictDecreasingWidths ys)
    (hmem : ∀ b, b ∈ xs ↔ b ∈ ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          exfalso
          have := (hmem y).mpr (by simp)
          simpa using this
  | cons x xs ih =>
      cases ys with
      | nil =>
          exfalso
          have := (hmem x).mp (by simp)
          simpa using this
      | cons y ys =>
          have hxmem : x = y ∨ x ∈ ys := by
            simpa using (hmem x).mp (by simp)
          have hymem : y = x ∨ y ∈ xs := by
            simpa using (hmem y).mpr (by simp)
          have hxy : x = y := by
            by_contra hne
            have hxys : x ∈ ys := hxmem.resolve_left hne
            have hyxs : y ∈ xs := hymem.resolve_left (Ne.symm hne)
            have hxyw := hx.head_gt hyxs
            have hyxw := hy.head_gt hxys
            omega
          subst y
          congr 1
          apply ih hx.tail hy.tail
          intro b
          constructor
          · intro hb
            have hall : b ∈ x :: ys := (hmem b).mp (by simp [hb])
            rcases List.mem_cons.mp hall with hbx | hbys
            · subst b
              exact False.elim (Nat.lt_irrefl _ (hx.head_gt hb))
            · exact hbys
          · intro hb
            have hall : b ∈ x :: xs := (hmem b).mpr (by simp [hb])
            rcases List.mem_cons.mp hall with hbx | hbxs
            · subst b
              exact False.elim (Nat.lt_irrefl _ (hy.head_gt hb))
            · exact hbxs

theorem strictDecreasingWidths_nodup {bs : List HexBridge}
    (hbs : StrictDecreasingWidths bs) : bs.Nodup := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.nodup_cons]
      refine ⟨?_, ih hbs.tail⟩
      intro hb
      exact Nat.lt_irrefl _ (hbs.head_gt hb)


end StatMech.Universality
