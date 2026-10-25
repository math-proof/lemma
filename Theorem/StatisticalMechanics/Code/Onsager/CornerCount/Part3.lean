/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2
import Def.StatisticalMechanics.Code.Onsager.CornerCount.Part3


namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


theorem turnList_eq (V : List Pt) :
    turnList V = List.zipWith turn (stepList V) ((stepList V).rotate 1) := rfl


theorem turnList_bounded (V : List Pt)
    (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
    ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1 := by
  intro t ht
  rw [turnList_eq] at ht
  obtain ⟨a, b, ha, hb, hc⟩ := mem_zipWith_imp turn (stepList V) ((stepList V).rotate 1) t ht
  have hb' : b ∈ stepList V := (List.mem_rotate).1 hb
  have := StatMech.Onsager.PolygonWalk.cross_unit_mem a b (hunit a ha) (hunit b hb')
  rw [hc]; exact this


theorem cornerBalanceL_eq_of_unit (V : List Pt)
    (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
    cornerBalanceL V = ccCount V - rcCount V :=
  cornerBalanceL_eq V (turnList_bounded V hunit)


theorem balanceL_split_of_counts (V : List Pt) (a b : ℕ)
    (hbV : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1)
    (hbA : ∀ t ∈ turnList (arc V a b), t = -1 ∨ t = 0 ∨ t = 1)
    (hbC : ∀ t ∈ turnList (coarc V a b), t = -1 ∨ t = 0 ∨ t = 1)
    (hcc : ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3)
    (hrc : rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1) :
    cornerBalanceL V = cornerBalanceL (arc V a b) + cornerBalanceL (coarc V a b) - 4 := by
  rw [cornerBalanceL_eq V hbV, cornerBalanceL_eq (arc V a b) hbA,
    cornerBalanceL_eq (coarc V a b) hbC]
  omega

end StatMech.Onsager.CornerCount
