/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_headAccum_nil (h : ℤ) : hexInfra_headAccum h [] = h := rfl

@[simp] theorem hexInfra_headAccum_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_headAccum h (t :: ts) = hexInfra_headAccum (h + t) ts := rfl


theorem hexInfra_verticesAux_ne_nil (m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.verticesAux m h ts ≠ [] := by
  cases ts with
  | nil => simp [HexWalk.verticesAux]
  | cons t ts => simp [HexWalk.verticesAux]


theorem hexInfra_verticesAux_getLast? (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.verticesAux m h ts).getLast?
      = some (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) := by
  induction ts generalizing m h with
  | nil => simp [HexWalk.verticesAux]
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, List.getLast?_cons, ih]
    simp


theorem hexInfra_verticesAux_getLast_mem (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)
      ∈ HexWalk.verticesAux m h ts :=
  List.mem_of_getLast? (hexInfra_verticesAux_getLast? m h ts)


end StatMech.Universality
