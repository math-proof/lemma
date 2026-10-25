/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part3


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp]
theorem midsAux_nil (m : ℂ) (h : ℤ) : midsAux m h [] = [m] := rfl

@[simp]
theorem midsAux_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    midsAux m h (t :: ts)
      = m :: midsAux (m + halfStep h + halfStep (h + t)) (h + t) ts := rfl

theorem length_midsAux (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (midsAux m h ts).length = ts.length + 1 := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp]
theorem length_mids (w : HexWalk) : w.mids.length = w.turns.length + 1 := by
  unfold mids; exact length_midsAux _ _ _


@[simp]
theorem mids_head (w : HexWalk) : (w.mids).headI = w.startMid := by
  unfold mids; cases w.turns with
  | nil => rfl
  | cons t ts => rfl


end HexWalk
end StatMech.Universality
