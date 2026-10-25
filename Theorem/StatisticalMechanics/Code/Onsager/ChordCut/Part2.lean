/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.Onsager.ChordCut


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


theorem reflex_continuation_interior (din dout : Pt)
    (_hd : isDir din) (hrefl : cross din dout = -1) :
    cross din din = 0 ∧ 0 < cross dout din := by
  refine ⟨by simp [cross]; ring, ?_⟩
  have h := cross_antisymm din dout
  omega


theorem convex_continuation_exterior (din dout : Pt) (hconv : cross din dout = 1) :
    cross dout din < 0 := by
  have h := cross_antisymm din dout
  omega


theorem continuation_not_exterior (din : Pt) (hd : isDir din) :
    din.1 * (-din).1 + din.2 * (-din).2 < 0 := by
  rcases hd with h | h | h | h <;> subst h <;> decide


end StatMech.Onsager.ChordCut
