/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
open Set SimpleGraph
open StatMech StatMech.Lattice


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

set_option maxHeartbeats 800000


theorem bcor_origin_eq : (![0, 0] : Site 2) = 0 := by
  funext i; fin_cases i <;> rfl


theorem bcor_mem_box {a b : ℤ} {n : ℕ} (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    (![a, b] : Site 2) ∈ box 2 n := by
  rw [mem_box]
  intro i; fin_cases i
  · simpa using ha
  · simpa using hb


theorem bcor_uIcc_natAbs {s t : ℤ} {n : ℕ} (hs : s.natAbs ≤ n) (ht : t ∈ Set.uIcc 0 s) :
    t.natAbs ≤ n := by
  rw [Set.mem_uIcc] at ht
  omega


end StatMech.Walls
