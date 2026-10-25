/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2
import Def.StatisticalMechanics.Code.Onsager.CellEuler


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


theorem cornerCount_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) (v : ℤ × ℤ) :
    cornerCount (insert c S) v = cornerCount S v + (if v ∈ cornersOf c then 1 else 0) := by
  unfold cornerCount
  rw [Finset.filter_insert]
  by_cases h : v ∈ cornersOf c
  · rw [if_pos h, if_pos h,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_filter]; exact fun h' => hc h'.1)]
  · rw [if_neg h, if_neg h, add_zero]


theorem cellVerts_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    cellVerts (insert c S) = cornersOf c ∪ cellVerts S := by
  unfold cellVerts
  rw [Finset.biUnion_insert]


end StatMech.Onsager.CellEuler
