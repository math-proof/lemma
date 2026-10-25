/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part4


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp]
theorem verticesAux_nil (m : ℂ) (h : ℤ) : verticesAux m h [] = [m + halfStep h] := rfl

@[simp]
theorem verticesAux_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    verticesAux m h (t :: ts)
      = (m + halfStep h) :: verticesAux (m + halfStep h + halfStep (h + t)) (h + t) ts := rfl

theorem length_verticesAux (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (verticesAux m h ts).length = ts.length + 1 := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih => simp [ih]


@[simp]
theorem length_vertices (w : HexWalk) : w.vertices.length = w.turns.length + 1 := by
  unfold vertices; exact length_verticesAux _ _ _


end HexWalk
end StatMech.Universality
