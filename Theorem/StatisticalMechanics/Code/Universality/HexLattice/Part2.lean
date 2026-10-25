/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part2


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp]
theorem headingsAux_nil (h : ℤ) : headingsAux h [] = [h] := rfl

@[simp]
theorem headingsAux_cons (h t : ℤ) (ts : List ℤ) :
    headingsAux h (t :: ts) = h :: headingsAux (h + t) ts := rfl


theorem length_headingsAux (h : ℤ) (ts : List ℤ) :
    (headingsAux h ts).length = ts.length + 1 := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp]
theorem length_headings (w : HexWalk) : w.headings.length = w.turns.length + 1 := by
  unfold headings; exact length_headingsAux _ _


@[simp]
theorem headings_head (w : HexWalk) : (w.headings).headI = w.h0 := by
  unfold headings; cases w.turns with
  | nil => rfl
  | cons t ts => rfl


end HexWalk
end StatMech.Universality
