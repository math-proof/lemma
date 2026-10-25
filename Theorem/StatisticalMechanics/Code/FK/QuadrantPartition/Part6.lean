/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part8
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section BoxGeom

theorem qp_boxTag_some_iff (d K : ℕ) (x : boxVerts d (2 * K + 1)) (s : Fin d → Bool) :
    qp_boxTag d K x = some s ↔ ∀ i, if s i then (1 ≤ (x : Site d) i ∧ (x : Site d) i ≤ 2 * K + 1)
              else (-(2 * K + 1 : ℤ) ≤ (x : Site d) i ∧ (x : Site d) i ≤ -1) := by
  unfold qp_boxTag
  by_cases hz : ∃ i, (x : Site d) i = 0
  · rw [if_pos hz]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; obtain ⟨i, hi⟩ := hz
      have hh := h i
      have hb := (qp_natAbs_iff ((x : Site d) i) (2 * K + 1)).mp (by have := x.2 i; push_cast; omega)
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hh <;>
        push_cast at hh <;> omega
  · rw [if_neg hz]
    push_neg at hz
    constructor
    · intro h
      rw [Option.some_inj] at h
      intro i
      have hb := (qp_natAbs_iff ((x : Site d) i) (2 * K + 1)).mp (by have := x.2 i; push_cast; omega)
      have hsi : s i = decide (0 < (x : Site d) i) := by rw [← h]
      by_cases hs : s i <;> simp only [hs] at hsi ⊢ <;>
        simp only [if_true, Bool.false_eq_true, if_false]
      · have hpos : 0 < (x : Site d) i :=
          (decide_eq_true_iff (p := 0 < (x : Site d) i)).mp hsi.symm
        have hnz := hz i; push_cast; omega
      · have hnp : ¬ (0 < (x : Site d) i) :=
          (decide_eq_false_iff_not (p := 0 < (x : Site d) i)).mp hsi.symm
        have hnz := hz i; push_cast; omega
    · intro h
      rw [Option.some_inj]; funext i
      have hh := h i
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hh ⊢
      · exact (decide_eq_true_iff (p := 0 < (x : Site d) i)).mpr (by omega)
      · exact (decide_eq_false_iff_not (p := 0 < (x : Site d) i)).mpr (by push_cast; omega)


end BoxGeom
end FK
end StatMech
