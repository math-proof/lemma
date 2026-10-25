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
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part6
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

noncomputable def qp_quadφ (d K : ℕ) (s : Fin d → Bool) :
    boxVerts d K ≃ {x : boxVerts d (2 * K + 1) // qp_boxTag d K x = some s} where
  toFun y := ⟨⟨fun i => (y : Site d) i + qp_vshift d K s i, by
      intro i; have hy := (qp_natAbs_iff ((y : Site d) i) K).mp (y.2 i)
      rw [qp_natAbs_iff]; simp only [qp_vshift]
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] <;> omega⟩,
    by rw [qp_boxTag_some_iff]; intro i; have hy := (qp_natAbs_iff ((y : Site d) i) K).mp (y.2 i)
       simp only [qp_vshift]
       by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] <;>
         push_cast <;> omega⟩
  invFun x := ⟨fun i => (x.1 : Site d) i - qp_vshift d K s i, by
      intro i
      have hP : (if s i then (1 ≤ (x.1.1 : Site d) i ∧ (x.1.1 : Site d) i ≤ 2 * K + 1)
              else (-(2 * K + 1 : ℤ) ≤ (x.1.1 : Site d) i ∧ (x.1.1 : Site d) i ≤ -1)) :=
        (qp_boxTag_some_iff d K x.1 s).mp x.2 i
      rw [qp_natAbs_iff]; simp only [qp_vshift]
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hP ⊢ <;>
        push_cast <;> omega⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; apply Subtype.ext; funext i; simp


end BoxGeom
end FK
end StatMech
